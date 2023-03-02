package org.lbee.twophase;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.config.FormalInstrumentationConfig;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.jfr.JFRTraceProducer;
import org.lbee.twophase.models.Message;

import java.io.*;
import java.net.Socket;

public abstract class Manager implements NamedClient {

    // Network manager
    protected final NetworkManager networkManager;
    // Instrumentation
    protected final TraceInstrumentation<JFRTraceProducer> instrumentation;
    //
    private boolean shutdown;

    /**
     * Is the manager has been shutdown
     * @return True if manager has been shutdown
     */
    public boolean isShutdown() { return shutdown; }

    /**
     * Shutdown the manager
     */
    protected void shutdown() { shutdown = true; }

    public Manager(Socket socket) throws IOException {
        this.networkManager = new NetworkManager(socket);
        this.shutdown = false;
        instrumentation = new TraceInstrumentation<>(new FormalInstrumentationConfig("JFR", true), new JFRTraceProducer());
    }

    protected void run() throws IOException, TraceProducerException {
        // Try to receive message for addressed to this process
        Message message = networkManager.receive(this.getName());

        // No message, return
        if (message == null)
            return;

        System.out.printf("%s - %s receive message: `%s`...\n", this.instrumentation.getClock(), this.getName(), message.getContent());
        // Sync process clock
        this.instrumentation.getClock().sync(message.getSenderClock());

        // Calls receive with received message
        receive(message);
    }

    abstract void receive(Message message) throws IOException, TraceProducerException;

}
