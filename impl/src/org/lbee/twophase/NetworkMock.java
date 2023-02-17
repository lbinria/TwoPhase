package org.lbee.twophase;

import java.util.HashMap;
import java.util.concurrent.ArrayBlockingQueue;

/**
 * Network mock, simulate network
 */
public class NetworkMock {

    private final HashMap<String, ArrayBlockingQueue<Message>> messageQueues;

    public NetworkMock() {
        this.messageQueues = new HashMap<>();
    }

    public void addProcess(TLANamedProcess process) {
        this.messageQueues.put(process.getName(), new ArrayBlockingQueue<>(10));
    }

    /**
     * Send a message to another process
     * @param to Receiver process name
     * @param message Message to send
     */
    public void put(String to, Message message) {
        this.messageQueues.get(to).add(message);
    }

    /**
     * Take message assign to a process
     * @param processName Process name
     * @return Received message
     * @throws InterruptedException
     */
    public Message take(String processName) throws InterruptedException {
        ArrayBlockingQueue<Message> messageQueue = this.messageQueues.get(processName);
        return messageQueue.isEmpty() ? null : this.messageQueues.get(processName).take();
    }

}
