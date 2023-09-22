package org.lbee.protocol;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.SharedClock;
import org.lbee.network.NetworkManager;

import java.io.*;

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
     * 
     * @return True if manager has been shutdown
     */
    public boolean isShutdown() {
        return shutdown;
    }

    /**
     * Shutdown the manager
     */
    protected void shutdown() {
        shutdown = true;
    }

    public Manager(String name, NetworkManager networkManager) throws IOException {
        this.name = name;
        this.networkManager = networkManager;
        this.shutdown = false;

        this.spec = BehaviorRecorder.create(name + ".ndjson", SharedClock.get("twophase.clock"));
        this.specMessages = spec.getVariable("msgs");
    }

    public abstract void run() throws IOException ;

}
