package org.lbee.twophase;

import java.util.HashMap;
import java.util.concurrent.Callable;

/**
 * Simulate a resource manager node (as a process)
 */
public class ResourceManager implements Callable<Void>, TLANamedProcess, NetworkProcess {


    private final NetworkMock networkMock;

    enum ResourceManagerState {
        WORKING,
        PREPARED,
        COMMITTED,
        ABORTED
    }

    // Logger
    private final TLALogger logger;
    // Process name
    private final String name;
    // Transaction manager (to send message)
    private final TransactionManager transactionManager;
    // Configuration of manager
    private final ResourceManagerConfiguration config;

    //private long clock;
    private final LogicalClock logicalClock;

    // TLA variables

    // Current state
    @TLAVariable(name="rmState")
    private ResourceManagerState state = ResourceManagerState.WORKING;

    // Last message sent
    @TLAVariable(name = "msgs")
    private String lastMessage;

    /**
     * Constructor
     * @param name Manager name
     * @param transactionManager Transaction manager to send message
     * @param config Manager configuration
     */
    public ResourceManager(NetworkMock networkMock, String name, TransactionManager transactionManager, ResourceManagerConfiguration config) {
        this.name = name;
        this.transactionManager = transactionManager;
        this.config = config;
        this.logger = new TLALogger();
        this.networkMock = networkMock;
        this.logicalClock = new LogicalClock();
    }

    @Override
    public Void call() throws Exception {

        System.out.printf("Task duration of %s: %s.\n", this.name, this.config.taskDuration);

        /* Task fail eventually */
        if (this.config.shouldFail)
            throw new Exception();


        // Block threads until resource manager was committed or aborted
        while (!(isCommitted() || isAborted())) {

            /* Resource manager is prepared to commit */
            if (isWorking() && Helper.next(10000) == 1) {
                // Simulate task before resource manager is prepared
                //Thread.sleep(config.taskDuration);
                this.prepare();
            }

            // Receive messages
            this.receive();
        }

        return null;
    }

    private boolean isWorking() {
        return this.getState() == ResourceManagerState.WORKING;
    }

    private boolean isCommitted() {
        return this.getState() == ResourceManagerState.COMMITTED;
    }

    private boolean isAborted() {
        return this.getState() == ResourceManagerState.ABORTED;
    }

    /**
     * @TLA-action RMPrepare(r)
     */
    protected void prepare()
    {
        this.setState(ResourceManagerState.PREPARED);
        this.send(new Message(this.name, TwoPhaseMessage.PREPARED.toString(), this.logicalClock.getValue()));
    }

    /**
     * @TLA-action RMRcvCommitMsg(r)
     */
    protected void commit() {
        // Simulate some task that take some time
        long d = 150 + Helper.next(2000);
        //System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(), d);
        try {Thread.sleep(d); } catch (InterruptedException ex) {}
        this.setState(ResourceManagerState.COMMITTED);
    }

    /**
     * @TLA-action RMRcvAbortMsg(r)
     */
    protected void abort()
    {
        // Simulate some task that take some time
        long d = 150 + Helper.next(2000);
        //System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(), d);
        try {Thread.sleep(d); } catch (InterruptedException ex) {}
        this.setState(ResourceManagerState.ABORTED);
    }

    /**
     * Send message to transaction manager
     * @param message Message to send
     */
    @Override
    public void send(Message message) {
        System.out.printf("%s - %s send message: `%s`...\n", this.logicalClock, this.getName(), message.content());
        // Simulate delay to send
        try { Thread.sleep(Helper.next(200)); } catch (InterruptedException ex) {}
        // Send message
        this.networkMock.put(transactionManager.getName(), message);
    }

    /**
     * Receive message from transaction manager
     */
    @Override
    public void receive() throws InterruptedException {
        Message message = this.networkMock.take(this.getName());
        if (message == null)
            return;

        System.out.printf("%s - %s receive message: `%s`...\n", this.logicalClock, this.getName(), message.content());
        // Sync process clock
        this.logicalClock.sync(message.senderClock());

        // Redirect message to method to execute
        switch (message.content()) {
            case "Commit" -> this.commit();
            case "Abort" -> this.abort();
            /* Nothing to do */
            default -> {}
        }

    }


    /**
     * Get process name
     * @return Process name
     */
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
    private void setState(ResourceManagerState state) {
        System.out.printf("%s - %s.state = %s.\n", this.logicalClock, this.getName(), state.toString());
        this.state = state;
    }

    /**
     * Get state of manager
     * @return Current state of manager
     */
    public ResourceManagerState getState() {
        return this.state;
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
     * @param prepareAnyway Prepare resource manager even if is not in "working" state (introduce error in implementation)
     */
    record ResourceManagerConfiguration(boolean shouldFail, int taskDuration, boolean prepareAnyway) {

        ResourceManagerConfiguration(boolean shouldFail, int taskDuration, boolean prepareAnyway) {
            this.shouldFail = shouldFail;
            this.prepareAnyway = prepareAnyway;

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
