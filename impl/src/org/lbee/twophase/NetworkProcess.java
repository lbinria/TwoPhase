package org.lbee.twophase;

interface NetworkProcess {

    void send(Message message);
    void receive() throws InterruptedException;

}
