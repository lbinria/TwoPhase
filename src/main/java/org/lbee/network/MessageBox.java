package org.lbee.network;

import org.lbee.protocol.Message;

/**
 * A message box
 */
public interface MessageBox {

    /**
     * Put a message into the box
     * @param message Message to put in the box
     */
    void put(Message message);

    /**
     * Take a message from the box
     * @return Message get from the box
     */
    Message take();
}
