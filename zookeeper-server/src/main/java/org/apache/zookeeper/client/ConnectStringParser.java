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

package org.apache.zookeeper.client;

import static org.apache.zookeeper.common.StringUtils.split;
import java.net.InetSocketAddress;
import java.util.ArrayList;
import java.util.List;
import org.apache.zookeeper.common.NetUtils;
import org.apache.zookeeper.common.PathUtils;

/**
 * A parser for ZooKeeper Client connect strings.
 *
 * This class is not meant to be seen or used outside of ZooKeeper itself.
 *
 * The chrootPath member should be replaced by a Path object in issue
 * ZOOKEEPER-849.
 *
 * @see org.apache.zookeeper.ZooKeeper
 */
public final class ConnectStringParser {

    private static final int DEFAULT_PORT = 2181;

    // Namespace
    private final String chrootPath;

    private final ArrayList<InetSocketAddress> serverAddresses = new ArrayList<>();

    /**
     * Parse host and port by spliting client connectString
     * with support for IPv6 literals
     * @throws IllegalArgumentException
     *             for an invalid chroot path.
     *
     * 可以在connectString中设置客户端连接上ZooKeeper后的根目录，
     * 方法是在host：port字符串之后添加上这个根目录，例如，192.168.1.1:2181，192.168.1.2:2181，192.168.1.3:2181/zk-book，
     * 这样就指定了该客户端连接上ZooKeeper服务器之后，所有对ZooKeeper的操作，都会基于这个根目录。
     * 例如，客户端对/foo/bar的操作，都会指向节点/zk-book/foo/bar这个目录也叫Chroot，即客户端隔离命名空间
     */
    public ConnectStringParser(String connectString) {
        // parse out chroot, if any
        int off = connectString.indexOf('/');
        if (off >= 0) {
            String chrootPath = connectString.substring(off);
            // ignore "/" chroot spec, same as null
            if (chrootPath.length() == 1) {
                this.chrootPath = null;
            } else {
                PathUtils.validatePath(chrootPath);
                this.chrootPath = chrootPath;
            }
            connectString = connectString.substring(0, off);
        } else {
            this.chrootPath = null;
        }

        List<String> hostsList = split(connectString, ",");
        for (String host : hostsList) {
            int port = DEFAULT_PORT;
            String[] hostAndPort = NetUtils.getIPV6HostAndPort(host);
            if (hostAndPort.length != 0) {
                host = hostAndPort[0];
                if (hostAndPort.length == 2) {
                    port = Integer.parseInt(hostAndPort[1]);
                }
            } else {
                int pidx = host.lastIndexOf(':');
                if (pidx >= 0) {
                    // otherwise : is at the end of the string, ignore
                    if (pidx < host.length() - 1) {
                        port = Integer.parseInt(host.substring(pidx + 1));
                    }
                    host = host.substring(0, pidx);
                }
            }
            serverAddresses.add(InetSocketAddress.createUnresolved(host, port));
        }
    }

    public String getChrootPath() {
        return chrootPath;
    }

    public ArrayList<InetSocketAddress> getServerAddresses() {
        return serverAddresses;
    }

}
