package org.lbee.twophase;

import java.util.HashMap;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * Network mock, simulate network
 */
public class NetworkMock {

//    private final HashMap<String, ArrayBlockingQueue<Message>> messageQueues;
    private final HashMap<String, ConcurrentLinkedQueue<Message>> messageQueues;

    public NetworkMock() {
        this.messageQueues = new HashMap<>();
    }

    public void addProcess(TLANamedProcess process) {
        this.messageQueues.put(process.getName(), new ConcurrentLinkedQueue<>());
    }

    /**
     * Send a message to another process
     * @param message Message to send
     */
    public void put(Message message) {
        if (!this.messageQueues.containsKey(message.getTo()))
            this.messageQueues.put(message.getTo(), new ConcurrentLinkedQueue<>());

        this.messageQueues.get(message.getTo()).add(message);
    }

    /**
     * Take message assign to a process
     * @param processName Process name
     * @return Received message
     * @throws InterruptedException
     */
    public Message take(String processName) throws InterruptedException {
        ConcurrentLinkedQueue<Message> messageQueue = this.messageQueues.get(processName);
        if (messageQueue == null)
            return null;

        return messageQueue.isEmpty() ? null : this.messageQueues.get(processName).poll();
    }

}
