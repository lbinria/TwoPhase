package org.lbee;

import org.lbee.models.Message;

import java.util.HashMap;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * Bucket where processes can pick some received messages
 */
public class MessageBucket {

    // Queue of messages by recipient
    private final HashMap<String, ConcurrentLinkedQueue<Message>> messageQueues;

    public MessageBucket() {
        this.messageQueues = new HashMap<>();
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
     * Take message of some addressee process (if any)
     * @param recipientName Recipient process name
     * @return Received message
     * @throws InterruptedException
     */
    public Message take(String recipientName) throws InterruptedException {
        // Get message queue of recipient
        ConcurrentLinkedQueue<Message> messageQueue = this.messageQueues.get(recipientName);
        // Not message queue, return null
        if (messageQueue == null)
            return null;

        // No message for recipient, return null, else get the first message
        return messageQueue.isEmpty() ? null : this.messageQueues.get(recipientName).poll();
    }

}
