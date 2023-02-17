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
        this.messageQueues.put(process.getName(), new ArrayBlockingQueue<Message>(Integer.MAX_VALUE));
    }

    /**
     * Send a message to another process
     * @param message Message to send
     */
    public void put(Message message) {
        if (!this.messageQueues.containsKey(message.getTo()))
            this.messageQueues.put(message.getTo(), new ArrayBlockingQueue<Message>(Integer.MAX_VALUE));

        this.messageQueues.get(message.getTo()).add(message);
    }

    /**
     * Take message assign to a process
     * @param processName Process name
     * @return Received message
     * @throws InterruptedException
     */
    public Message take(String processName) throws InterruptedException {
        ArrayBlockingQueue<Message> messageQueue = this.messageQueues.get(processName);
        if (messageQueue == null)
            return null;

        return messageQueue.isEmpty() ? null : this.messageQueues.get(processName).take();
    }

}
