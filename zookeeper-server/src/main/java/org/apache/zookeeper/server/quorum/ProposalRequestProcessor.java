/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.zookeeper.server.quorum;

import org.apache.zookeeper.server.Request;
import org.apache.zookeeper.server.RequestProcessor;
import org.apache.zookeeper.server.ServerMetrics;
import org.apache.zookeeper.server.SyncRequestProcessor;
import org.apache.zookeeper.server.quorum.Leader.XidRolloverException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This RequestProcessor simply forwards requests to an AckRequestProcessor and
 * SyncRequestProcessor.
 *
 * ProposalRequestProcessor处理器是Leader服务器的事务投票处理器，也是Leader服务器事务处理流程的发起者。
 * 对于非事务请求，ProposalRequestProcessor会直接将请求流转到CommitProcessor处理器，不再做其他处理；而对于事务请求，
 * 除了将请求交给CommitProcessor处理器外，还会根据请求类型创建对应的Proposal提议，并发送给所有的Follower 服务器来发起一次集群内的事务投票。
 * 同时，ProposaLRequestProcessor还会将事务请求交付给 SyncRequestProcessor进行事务日志的记录。
 */
public class ProposalRequestProcessor implements RequestProcessor {

    private static final Logger LOG = LoggerFactory.getLogger(ProposalRequestProcessor.class);

    LeaderZooKeeperServer zks;

    RequestProcessor nextProcessor;

    SyncRequestProcessor syncProcessor;

    // If this property is set, requests from Learners won't be forwarded
    // to the CommitProcessor in order to save resources
    public static final String FORWARD_LEARNER_REQUESTS_TO_COMMIT_PROCESSOR_DISABLED =
          "zookeeper.forward_learner_requests_to_commit_processor_disabled";
    private final boolean forwardLearnerRequestsToCommitProcessorDisabled;

    public ProposalRequestProcessor(LeaderZooKeeperServer zks, RequestProcessor nextProcessor) {
        this.zks = zks;
        this.nextProcessor = nextProcessor;
        AckRequestProcessor ackProcessor = new AckRequestProcessor(zks.getLeader());
        syncProcessor = new SyncRequestProcessor(zks, ackProcessor);

        forwardLearnerRequestsToCommitProcessorDisabled = Boolean.getBoolean(
                FORWARD_LEARNER_REQUESTS_TO_COMMIT_PROCESSOR_DISABLED);
        LOG.info("{} = {}", FORWARD_LEARNER_REQUESTS_TO_COMMIT_PROCESSOR_DISABLED,
                forwardLearnerRequestsToCommitProcessorDisabled);
    }

    /**
     * initialize this processor
     */
    public void initialize() {
        syncProcessor.start();
    }

    public void processRequest(Request request) throws RequestProcessorException {
        /* In the following IF-THEN-ELSE block, we process syncs on the leader.
         * If the sync is coming from a follower, then the follower
         * handler adds it to syncHandler. Otherwise, if it is a client of
         * the leader that issued the sync command, then syncHandler won't
         * contain the handler. In this case, we add it to syncHandler, and
         * call processRequest on the next processor.
         */
        // 来自learn的同步请求
        if (request instanceof LearnerSyncRequest) {
            zks.getLeader().processSync((LearnerSyncRequest) request);
        } else {
            if (shouldForwardToNextProcessor(request)) {
                // 提交到CommitProcessor的处理队列（起缓冲作用）
                nextProcessor.processRequest(request);
            }
            // 事务 类型的 Transactions ---> 需要就集群同步
            if (request.getHdr() != null) {
                // We need to sync and get consensus on any transactions
                try {
                    // 发起提案，向Follower发送PROPOSAL请求
                    zks.getLeader().propose(request);
                } catch (XidRolloverException e) {
                    throw new RequestProcessorException(e.getMessage(), e);
                }
                // 执行 SyncRequestProcessor （会将请求追加事务日志）以及
                // 下一个 AckRequestProcessor（该处理器会等待到达大于一半的follower的ack之后发送Commit请求）
                syncProcessor.processRequest(request);
            }
        }
    }

    public void shutdown() {
        LOG.info("Shutting down");
        nextProcessor.shutdown();
        syncProcessor.shutdown();
    }

    /**
     * 启用 (false)：当 zookeeper.forward_learner_requests_to_commit_processor_disabled 被设置为 false 时（这是默认值），
     * 来自 Learner 节点的请求将被转发到 Commit Processor 进行处理。这意味着 Leader 将处理并提交这些事务性请求，从而保证数据的一致性。
     *
     * 禁用 (true)：当 zookeeper.forward_learner_requests_to_commit_processor_disabled 被设置为 true 时，
     * 来自 Learner 节点的请求将不会被转发到 Commit Processor。这可能用于某些优化场景或者特殊配置下，减少 Leader 处理请求的负载。
     * @param request
     * @return
     */
    private boolean shouldForwardToNextProcessor(Request request) {
        if (!forwardLearnerRequestsToCommitProcessorDisabled) {
            return true;
        }
        if (request.getOwner() instanceof LearnerHandler) {
            ServerMetrics.getMetrics().REQUESTS_NOT_FORWARDED_TO_COMMIT_PROCESSOR.add(1);
            return false;
        }
        return true;
    }
}
