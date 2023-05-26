package org.lbee;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.VirtualField;
import org.lbee.models.Message;
import org.lbee.models.TwoPhaseMessage;

import java.io.IOException;
import java.net.Socket;
import java.util.Locale;
import java.util.Map;
import java.util.Random;

public class ResourceManager extends Manager implements NamedClient {

    /**
     * Possible states of resource manager
     */
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

    // Current state
    private ResourceManagerState state = ResourceManagerState.WORKING;

    private final VirtualField specState;

    /**
     * Construct a resource manager
     * @param socket Client socket
     * @param name Resource manager name
     * @param transactionManagerName Attached transaction manager name
     * @param config Resource manager config
     * @throws IOException Throw when errors occur on socket
     */
    public ResourceManager(Socket socket, String name, String transactionManagerName, ResourceManagerConfiguration config) throws IOException {
        super(name, socket);
        this.config = config;
        this.transactionManagerName = transactionManagerName;
        specState = spec.getVariable("rmState").getField(getName());
    }

    private void reset() {
        setState(ResourceManagerState.WORKING);
//        spec.commitChanges("RMReset");
    }
    /**
     * Set state of manager
     * @param state New manager state
     */
    private void setState(ResourceManagerState state) {
        // Change state
        this.state = state;
//        specState.set(state.toString().toLowerCase(Locale.ROOT));
    }

    /**
     * Get state of manager
     * @return Current state of manager
     */
    public ResourceManagerState getState() {
        return this.state;
    }

    @Override
    public void run() throws IOException, TraceProducerException {
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

        /* Task fail eventually */
        if (this.config.shouldFail)
            throw new IOException();
    }

    @Override
    protected void receive(Message message) throws IOException, TraceProducerException {
        // Redirect message to method to execute
        switch (message.getContent()) {
            case "Commit" -> this.commit();
            case "Abort" -> this.abort();
            /* Nothing to do */
            default -> {}
        }
    }

    protected void register() throws IOException {
        System.out.println("Registering...");
        this.networkManager.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.REGISTER.toString(), 0));
    }

    /**
     * @TLA-action RMPrepare(r)
     */
    protected void prepare() throws IOException, TraceProducerException {
        this.setState(ResourceManagerState.PREPARED);
        specMessages.add(Map.of("type","Prepared", "rm", getName()));
        spec.commitChanges("RMPrepare");
        this.networkManager.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.PREPARED.toString(), 0));
    }

    /**
     * @TLA-action RMRcvCommitMsg(r)
     */
    protected void commit() throws TraceProducerException {
        // Simulate some task that take some time
        long d = 150 + Helper.next(1000);
        //System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(), d);
        try {Thread.sleep(d); } catch (InterruptedException ex) {}
        this.setState(ResourceManagerState.COMMITTED);
//        spec.commitChanges("RMRcvCommitMsg");
        // Shutdown process
        this.reset();
        this.shutdown();
    }

    /**
     * @TLA-action RMRcvAbortMsg(r)
     */
    protected void abort() throws TraceProducerException {
        // Simulate some task that take some time
        long d = 150 + Helper.next(2000);
        //System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(), d);
        try {Thread.sleep(d); } catch (InterruptedException ex) {}
        this.setState(ResourceManagerState.ABORTED);
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
                //this.taskDuration = new Random().nextInt(10000);
                this.taskDuration = new Random().nextInt(100);
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

    /**
     * Check whether the manager is in working state
     * @return True if manager is in working state, else false
     */
    private boolean isWorking() {
        return this.getState() == ResourceManagerState.WORKING;
    }

    /**
     * Check whether the manager is in committed state
     * @return True if manager is in committed state, else false
     */
    private boolean isCommitted() {
        return this.getState() == ResourceManagerState.COMMITTED;
    }

    /**
     * Check whether the manager is in aborted state
     * @return True if manager is in aborted state, else false
     */
    private boolean isAborted() {
        return this.getState() == ResourceManagerState.ABORTED;
    }

}
