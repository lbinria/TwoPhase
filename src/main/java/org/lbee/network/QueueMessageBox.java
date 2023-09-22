package org.lbee.network;

import org.lbee.protocol.Message;

import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * A message box
 * Messages are taken as FIFO order
 */
public class QueueMessageBox implements MessageBox {

    /**
     * Messages of the box
     */
    private final Queue<Message> messages;

    public QueueMessageBox() {
        messages = new ConcurrentLinkedQueue<>();
    }

    /**
     * Put a message into the box
     * @param message Message to put in the box
     */
    @Override
    public void put(Message message) {
        messages.add(message);
    }

    /**
     * Poll message from the box
     * @return Message get from the box
     */
    @Override
    public Message take() {
        // No message for recipient, return null, else get the first message
        return messages.isEmpty() ? null : messages.poll();
    }
}
