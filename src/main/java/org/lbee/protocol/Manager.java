package org.lbee.protocol;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.SharedClock;
import org.lbee.network.NetworkManager;

import java.io.*;
import java.net.Socket;

public abstract class Manager {

    // Manager name
    private final String name;
    // Network manager
    public final NetworkManager networkManager;

    protected final BehaviorRecorder spec;
    protected final VirtualField specMessages;

    private boolean shutdown;

    public String getName() {
        return name;
    }

    /**
     * Is the manager has been shutdown
     * @return True if manager has been shutdown
     */
    public boolean isShutdown() { return shutdown; }

    /**
     * Shutdown the manager
     */
    protected void shutdown() { shutdown = true; }

    public Manager(String name, Socket socket) throws IOException {
        this.name = name;
        this.networkManager = new NetworkManager(socket);
        this.shutdown = false;

        this.spec = BehaviorRecorder.create(name + ".ndjson", SharedClock.get("twophase.clock"));
        this.specMessages = spec.getVariable("msgs");
    }

    public void run() throws IOException {
        // Try to receive message for addressed to this process
        Message message = networkManager.receive(this.getName());

        // No message, return
        if (message == null)
            return;

        // Calls receive with received message
        receive(message);
    }

    abstract void receive(Message message) throws IOException;

}
