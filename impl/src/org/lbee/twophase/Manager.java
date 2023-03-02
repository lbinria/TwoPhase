package org.lbee.twophase;

import org.lbee.instrumentation.FormalInstrumentation;
import org.lbee.instrumentation.FormalInstrumentationConfig;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.jfr.JFRTraceProducer;
import org.lbee.twophase.models.Message;

import java.io.*;
import java.net.Socket;

public abstract class Manager implements NamedClient {

    protected final NetworkManager networkManager;

    protected final FormalInstrumentation<JFRTraceProducer> instrumentation;

    private boolean shutdown;

    public boolean isShutdown() { return shutdown; }
    protected void shutdown() { shutdown = true; }

    public Manager(Socket socket) throws IOException {
        this.networkManager = new NetworkManager(socket);
        this.shutdown = false;
        instrumentation = new FormalInstrumentation<>(new FormalInstrumentationConfig("JFR", true), new JFRTraceProducer());
    }

    //abstract void run() throws IOException;

    protected void run() throws IOException, TraceProducerException {
        Message message = networkManager.receive(this.getName());

        if (message == null)
            return;

        System.out.printf("%s - %s receive message: `%s`...\n", this.instrumentation.getClock(), this.getName(), message.getContent());
        // Sync process clock
        this.instrumentation.getClock().sync(message.getSenderClock());

        // Call receive with received message
        receive(message);
    }

    abstract void receive(Message message) throws IOException, TraceProducerException;

}
