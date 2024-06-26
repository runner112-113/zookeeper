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

package org.apache.zookeeper.server.persistence;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class FilePadding {

    private static final Logger LOG;
    // 64MB
    /**
     * 该参数有默认值：65536，单位是KB，即64MB，可以不配置，仅支持系统属性方式配置：zookeeper.preAllocSize。
     * 参数preAllocSize用于配置ZooKeeper事务日志文件预分配的磁盘空间大小。
     * 通常情况下，我们使用ZooKeeper的默认配置65536KB即可，但是如果我们将参数snapcount设置得比默认值更小或更大，那么preAllocSize参数也要随之做出变更。
     * 举个例子来说：如果我们将snapCount的值设置为500，同时预估每次事务操作的数据量大小至多1KB，那么参数preAllocSize设置为500就足够了。
     */
    private static long preAllocSize = 65536 * 1024;
    private static final ByteBuffer fill = ByteBuffer.allocateDirect(1);

    static {
        LOG = LoggerFactory.getLogger(FileTxnLog.class);

        String size = System.getProperty("zookeeper.preAllocSize");
        if (size != null) {
            try {
                preAllocSize = Long.parseLong(size) * 1024;
            } catch (NumberFormatException e) {
                LOG.warn("{} is not a valid value for preAllocSize", size);
            }
        }
    }

    private long currentSize;

    /**
     * Getter of preAllocSize has been added for testing
     */
    public static long getPreAllocSize() {
        return preAllocSize;
    }

    /**
     * method to allow setting preallocate size
     * of log file to pad the file.
     *
     * @param size the size to set to in bytes
     */
    public static void setPreallocSize(long size) {
        preAllocSize = size;
    }

    public void setCurrentSize(long currentSize) {
        this.currentSize = currentSize;
    }

    /**
     * pad the current file to increase its size to the next multiple of preAllocSize greater than the current size and position
     *
     * @param fileChannel the fileChannel of the file to be padded
     * @throws IOException
     */
    long padFile(FileChannel fileChannel) throws IOException {
        return this.padFile(fileChannel, fileChannel.position());
    }

    long padFile(FileChannel fileChannel, long position) throws IOException {
        // 判断文件是否需要扩容
        long newFileSize = calculateFileSizeWithPadding(position, currentSize, preAllocSize);
        if (currentSize != newFileSize) {
            fileChannel.write((ByteBuffer) fill.position(0), newFileSize - fill.remaining());
            currentSize = newFileSize;
        }
        return currentSize;
    }


    /**
     * Calculates a new file size with padding. We only return a new size if
     * the current file position is sufficiently close (less than 4K) to end of
     * file and preAllocSize is &gt; 0.
     *
     * @param position     the point in the file we have written to
     * @param fileSize     application keeps track of the current file size
     * @param preAllocSize how many bytes to pad
     * @return the new file size. It can be the same as fileSize if no
     * padding was done.
     *
     * 当检测到当前事务日志文件剩余空间不足4096字节（4KB）时，就会开始进行文件空间扩容。
     * 文件空间扩容的过程其实非常简单，就是在现有文件大小的基础上，将文件大小增加65536KB（64MB），然后使用“0”（\0）填充这些被扩容的文件空间。
     *
     */
    // VisibleForTesting
    public static long calculateFileSizeWithPadding(long position, long fileSize, long preAllocSize) {
        // If preAllocSize is positive and we are within 4KB of the known end of the file calculate a new file size
        if (preAllocSize > 0 && position + 4096 >= fileSize) {
            // If we have written more than we have previously preallocated we need to make sure the new
            // file size is larger than what we already have
            if (position > fileSize) {
                fileSize = position + preAllocSize;
                fileSize -= fileSize % preAllocSize;
            } else {
                fileSize += preAllocSize;
            }
        }

        return fileSize;
    }

}
