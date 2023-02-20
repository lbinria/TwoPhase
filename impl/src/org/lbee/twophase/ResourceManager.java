package org.lbee.twophase;

import java.io.IOException;
import java.net.Socket;
import java.util.Locale;
import java.util.Random;

public class ResourceManager extends NetworkProcess implements TLANamedProcess {

    enum ResourceManagerState {
        WORKING,
        PREPARED,
        COMMITTED,
        ABORTED
    }

    // Config
    private final ResourceManagerConfiguration config;
    // Transaction manager (to send message)
    private final String transactionManagerName;

    private final String name;

    // Current state
    //@TLAVariable(name="rmState")
    private ResourceManagerState state = ResourceManagerState.WORKING;

    /**
     * Set state of manager
     * @param state New manager state
     */
    private void setState(ResourceManagerState state) {
        System.out.printf("%s - %s.state = %s.\n", this.logicalClock, this.getName(), state.toString());
        this.state = state;
        // Log event (hard-coded for now)
        logger.log(this, "rmState", state.toString().toLowerCase(Locale.ROOT));
    }

    /**
     * Get state of manager
     * @return Current state of manager
     */
    public ResourceManagerState getState() {
        return this.state;
    }

    public ResourceManager(Socket socket, String name, String transactionManagerName, ResourceManagerConfiguration config) throws IOException {
        super(socket);
        this.config = config;
        this.transactionManagerName = transactionManagerName;
        this.name = name;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public void run() throws IOException {
        // Check eventual received message
        super.run();

        // If working simulate task, and then prepare
        if (this.getState() == ResourceManagerState.WORKING) {
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

    @Override
    protected void receive(Message message) throws IOException {
        // Redirect message to method to execute
        switch (message.getContent()) {
            case "Commit" -> this.commit();
            case "Abort" -> this.abort();
            /* Nothing to do */
            default -> {}
        }
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


    protected void register() throws IOException {
        System.out.println("Registering...");
        this.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.REGISTER.toString(), this.logicalClock.getValue()));
    }

    /**
     * @TLA-action RMPrepare(r)
     */
    protected void prepare() throws IOException {
        this.setState(ResourceManagerState.PREPARED);
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
        this.setState(ResourceManagerState.COMMITTED);
        // Commit events
        logger.commit();
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
        this.setState(ResourceManagerState.ABORTED);
        // Commit events
        logger.commit();
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
