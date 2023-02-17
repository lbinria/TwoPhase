package org.lbee.twophase;

import java.io.IOException;
import java.net.Socket;
import java.util.Random;

public class ResourceManager2 extends NetworkProcess2 {

    enum ResourceManagerState {
        WORKING,
        PREPARED,
        COMMITTED,
        ABORTED
    }

    // Logger
    private final TLALogger logger;
    // Config
    private final ResourceManagerConfiguration config;
    // Transaction manager (to send message)
    private final String transactionManagerName;

    private final String name;

    // Current state
    @TLAVariable(name="rmState")
    private ResourceManager.ResourceManagerState state = ResourceManager.ResourceManagerState.WORKING;

    /**
     * Set state of manager
     * @param state New manager state
     */
    private void setState(ResourceManager.ResourceManagerState state) {
        System.out.printf("%s - %s.state = %s.\n", this.logicalClock, this.getName(), state.toString());
        this.state = state;
    }

    /**
     * Get state of manager
     * @return Current state of manager
     */
    public ResourceManager.ResourceManagerState getState() {
        return this.state;
    }

    public ResourceManager2(Socket socket, String name, String transactionManagerName, ResourceManagerConfiguration config) throws IOException {
        super(socket);
        this.config = config;
        this.logger = new TLALogger();
        this.transactionManagerName = transactionManagerName;
        this.name = name;
    }

    @Override
    String getName() {
        return this.name;
    }

    @Override
    public void run() throws IOException {
        // Check eventual received message
        checkMessage();

        // If working simulate task, and then prepare
        if (this.getState() == ResourceManager.ResourceManagerState.WORKING) {
            try {
                Thread.sleep(config.taskDuration);
            } catch (InterruptedException ex) {
            }
            this.prepare();
        }
        //System.out.printf("Task duration of %s: %s.\n", this.getName(), this.config.taskDuration);

        /* Task fail eventually */
        if (this.config.shouldFail)
            throw new IOException();
    }

    protected void checkMessage() throws IOException {
        Message message = receive();

        if (message == null)
            return;

        System.out.printf("%s - %s receive message: `%s`...\n", this.logicalClock, this.getName(), message.getContent());
        // Sync process clock
        this.logicalClock.sync(message.getSenderClock());

        // Redirect message to method to execute
        switch (message.getContent()) {
            case "Commit" -> this.commit();
            case "Abort" -> this.abort();
            /* Nothing to do */
            default -> {}
        }
    }

    private boolean isWorking() {
        return this.getState() == ResourceManager.ResourceManagerState.WORKING;
    }

    private boolean isCommitted() {
        return this.getState() == ResourceManager.ResourceManagerState.COMMITTED;
    }

    private boolean isAborted() {
        return this.getState() == ResourceManager.ResourceManagerState.ABORTED;
    }


    protected void register() throws IOException {
        System.out.println("Registering...");
        this.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.REGISTER.toString(), this.logicalClock.getValue()));
    }

    /**
     * @TLA-action RMPrepare(r)
     */
    protected void prepare() throws IOException {
        this.setState(ResourceManager.ResourceManagerState.PREPARED);
        this.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.PREPARED.toString(), this.logicalClock.getValue()));
    }

    /**
     * @TLA-action RMRcvCommitMsg(r)
     */
    protected void commit() {
        // Simulate some task that take some time
        long d = 150 + Helper.next(2000);
        //System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(), d);
        try {Thread.sleep(d); } catch (InterruptedException ex) {}
        this.setState(ResourceManager.ResourceManagerState.COMMITTED);
        // Shutdown process
        this.shutdown();
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
        this.setState(ResourceManager.ResourceManagerState.ABORTED);
        // Shutdown process
        this.shutdown();
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
                this.taskDuration = new Random().nextInt(10000);
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
