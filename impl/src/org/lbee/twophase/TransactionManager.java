package org.lbee.twophase;

import java.util.HashSet;
import java.util.concurrent.Callable;

/**
 * Simulate a transaction manager node
 */
public class TransactionManager implements Callable<Void>, TLANamedProcess {

    // Logger
    private final TLALogger logger;

    private final TransactionManagerConfiguration config;

    private final String name;

    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Configuration of a resource manager
     * @param timeout Is resource manager should fail, invoke an unknown exception
     */
    record TransactionManagerConfiguration(int timeout) {
        @Override
        public String toString() {
            return "TransactionManagerConfiguration{" +
                    "timeout=" + timeout +
                    '}';
        }
    }

    // TLA variables

    // Current state of manager
    @TLAVariable(name = "tmState")
    private String state = "init";

    // Last message sent
    @TLAVariable(name = "msgs")
    private String lastMessage;

    // Last resource manager prepared
    @TLAVariable(name = "tmPrepared")
    private String lastPrepared;

    private final HashSet<ResourceManager> resourceManagers;
    private final HashSet<ResourceManager> preparedResourceManagers;
    private final long start;

    public TransactionManager(TransactionManagerConfiguration config) {
        this.name = "TM";
        this.config = config;
        this.preparedResourceManagers = new HashSet<ResourceManager>();
        this.resourceManagers = new HashSet<ResourceManager>();
        this.start = System.currentTimeMillis();
        this.logger = new TLALogger();
    }

    @Override
    public Void call() throws Exception {

        // Blocks task until transaction manager commit or abort
        while (!(this.checkCommit() || this.checkTimeout())) {}

        /* Only commit if all resource managers were prepared */
        if (this.checkCommit())
            this.commit();
        /* Only abort if timeout was reached */
        else if (this.checkTimeout())
            this.abort();

        // Nothing should never happen
        return null;
    }

    public void addResourceManager(ResourceManager resourceManager) {
        this.resourceManagers.add(resourceManager);
    }

    /**
     * @TLA-action TMCommit
     */
    private void commit()
    {
        //clock++;
        logger.sync(() -> {
            this.send("Commit");
            this.setState("done");
        });
    }

    /**
     * @TLA-action TMAbort
     */
    public void abort()
    {
        //clock++;
        logger.sync(() -> {
            this.send("Abort");
            this.setState("done");
        });
    }

    /**
     * @TLA-action TMRcvPrepared(r)
     * @TLA-variable tmPrepared
     */
    public void receivePrepared(ResourceManager sender) {
        //clock++;
        logger.sync(() -> {
            /* Add to prepared resource manager set */
            preparedResourceManagers.add(sender);
            // Log state change
            //new App2TLA.TLAEvent("TM", "tmPrepared", sender.getName(), clock).commit();
            setLastPrepared(sender.getName());
        });
    }

    /**
     * @TLA-variable msgs
     * @param message
     */
    protected void send(String message) {
        // Log message sent
        //new App2TLA.TLAEvent("TM", "msgs", message, clock).commit();
        setLastMessage(message);
        // Send message to all resource managers
        for (ResourceManager rm : this.resourceManagers) {
            rm.receive(message);
        }
    }

    protected void receive(ResourceManager sender, String message) {
        switch (message) {
            case "Prepared" -> this.receivePrepared(sender);
            /* Nothing to do */
            default -> {}
        }
    }


    public String getState() {
        return state;
    }

    private void setState(String state) {
        this.state = state;
        // Log state change
        //new App2TLA.TLAEvent("TM", "tmState", state, clock).commit();
        logger.notify(this, "state", this.state);
    }

    public void setLastMessage(String lastMessage) {
        this.lastMessage = lastMessage;
        logger.notify(this, "lastMessage", this.lastMessage);
    }

    public void setLastPrepared(String lastPrepared) {
        this.lastPrepared = lastPrepared;
        logger.notify(this, "lastPrepared", this.lastPrepared);
    }

    protected boolean checkCommit()  {
        return this.preparedResourceManagers.containsAll(this.resourceManagers);
    }

    protected boolean checkTimeout() {
        return System.currentTimeMillis() - this.start >= this.config.timeout;
    }

}
