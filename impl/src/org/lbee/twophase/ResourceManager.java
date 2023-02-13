package org.lbee.twophase;

import java.util.concurrent.Callable;

/**
 * Simulate a resource manager node (as a process)
 */
public class ResourceManager implements Callable<Void>, TLANamedProcess {

    // Logger
    private final TLALogger logger;
    // Process name
    private final String name;
    // Transaction manager (to send message)
    private final TransactionManager transactionManager;
    // Configuration of manager
    private final ResourceManagerConfiguration config;

    // TLA variables

    // Current state
    @TLAVariable(name="rmState")
    private String state = "working";

    // Last message sent
    @TLAVariable(name = "msgs")
    private String lastMessage;

    /**
     * Constructor
     * @param name Manager name
     * @param transactionManager Transaction manager to send message
     * @param config Manager configuration
     */
    public ResourceManager(String name, TransactionManager transactionManager, ResourceManagerConfiguration config) {
        this.name = name;
        this.transactionManager = transactionManager;
        this.config = config;
        this.logger = new TLALogger();
    }

    @Override
    public Void call() throws Exception {

        System.out.printf("Task duration of %s: %s.\n", this.name, this.config.taskDuration);
        /* Task fail eventually */
        if (this.config.shouldFail)
            throw new Exception();
        else
            /* Simulate some task */
            Thread.sleep(this.config.taskDuration);

        /* Resource manager is prepared to commit */
        if (this.getState().equals("working"))
            this.prepare();

        return null;
    }

    /**
     * @TLA-action RMPrepare(r)
     */
    protected void prepare()
    {
        //clock++;
        // Just one action take one unit of local logical time
        logger.sync(() -> {
            this.setState("prepared");
            this.send("Prepared");
        });
    }

    /**
     * @TLA-action RMRcvCommitMsg(r)
     */
    protected void commit()
    {
        //clock++;
        logger.sync(() -> {
            this.setState("committed");
        });
    }

    /**
     * @TLA-action RMRcvAbortMsg(r)
     */
    protected void abort()
    {
        //clock++;
        logger.sync(() -> {
            this.setState("aborted");
        });
    }

    /**
     * Send message to transaction manager
     * @param message Message to send
     */
    protected void send(String message) {
        // Log message sent
        //new App2TLA.TLAEvent(this.name, "msgs", message, clock).commit();
        this.setLastMessage(message);
        // Send message
        this.transactionManager.receive(this, message);
    }

    /**
     * Receive message from transaction manager
     * @param message Received message
     */
    protected void receive(String message)
    {
        // Redirect message to method to execute
        switch (message) {
            case "Commit" -> this.commit();
            case "Abort" -> this.abort();
            /* Nothing to do */
            default -> {}
        }

    }

    public String getName() { return this.name; }

    /**
     * Get transaction manager of resource manager
     * @return Transaction manager
     */
    public TransactionManager getTransactionManager() {
        return this.transactionManager;
    }

    /**
     * Set state of manager
     * @param state New manager state
     */
    private void setState(String state) {
        this.state = state;
        logger.notify(this, "state", state);
        // Log state change
        //new App2TLA.TLAEvent(this.name, "rmState", state, clock).commit();
    }

    /**
     * Get state of manager
     * @return Current state of manager
     */
    public String getState() {
        return this.state;
    }

    private void setLastMessage(String message) {
        this.lastMessage = message;
        logger.notify(this, "lastMessage", message);
    }

    @Override
    public String toString() {
        return "ResourceManager{" +
                "name='" + name + '\'' +
                '}';
    }

    /**
     * Configuration of a resource manager
     * @param shouldFail Is resource manager should fail, invoke an unknown exception
     * @param taskDuration Duration of the simulated task
     */
    record ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {

        ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {
            this.shouldFail = shouldFail;

            if (taskDuration == -1)
                /* Set a random task duration */
                this.taskDuration = Helper.next(10000);
            else
                this.taskDuration = taskDuration;
        }

        @Override
        public String toString() {
            return "ResourceManagerConfiguration{" +
                    "shouldFail=" + shouldFail +
                    ", taskDuration=" + taskDuration +
                    '}';
        }
    }

}
