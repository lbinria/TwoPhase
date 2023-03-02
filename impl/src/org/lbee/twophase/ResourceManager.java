package org.lbee.twophase;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.tla.value.TLARecordValue;
import org.lbee.instrumentation.tla.variable.TLARecordVariable;
import org.lbee.instrumentation.tla.variable.TLASetVariable;
import org.lbee.instrumentation.tla.value.TLAStringValue;
import org.lbee.twophase.models.Message;
import org.lbee.twophase.models.TwoPhaseMessage;

import java.io.IOException;
import java.net.Socket;
import java.util.Locale;
import java.util.Random;

public class ResourceManager extends Manager implements NamedClient {

    // Manager name
    private final String name;

    // Instrumented values
    private final TLARecordVariable instrumentedState;
    private final TLASetVariable<TLARecordValue> instrumentedMsgs;

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

    /**
     * Construct a resource manager
     * @param socket Client socket
     * @param name Resource manager name
     * @param transactionManagerName Attached transaction manager name
     * @param config Resource manager config
     * @throws IOException Throw when errors occur on socket
     */
    public ResourceManager(Socket socket, String name, String transactionManagerName, ResourceManagerConfiguration config) throws IOException {
        super(socket);
        this.name = name;
        this.config = config;
        this.transactionManagerName = transactionManagerName;

        // Here can be hold by configuration file
        this.instrumentedState = this.instrumentation.add("rmState", TLARecordVariable::new);
        this.instrumentedMsgs = this.instrumentation.add("msgs", TLASetVariable::new);
    }

    /**
     * Set state of manager
     * @param state New manager state
     */
    private void setState(ResourceManagerState state) throws TraceProducerException {
        // Print message
        System.out.printf("%s - %s.state = %s.\n", this.instrumentation.getClock(), this.getName(), state.toString());
        // Change state
        this.state = state;
        // Set new state value (hard-coded for now)
        instrumentedState.set(this.getName(), new TLAStringValue(state.toString().toLowerCase(Locale.ROOT)));
    }

    /**
     * Get state of manager
     * @return Current state of manager
     */
    public ResourceManagerState getState() {
        return this.state;
    }

    @Override
    public String getName() {
        return this.name;
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
        this.networkManager.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.REGISTER.toString(), this.instrumentation.getClock().getValue()));
    }

    /**
     * @TLA-action RMPrepare(r)
     */
    protected void prepare() throws IOException, TraceProducerException {
        this.setState(ResourceManagerState.PREPARED);

        // Send message
        TLAMsgs value = new TLAMsgs(new TLAStringValue("Prepared"), new TLAStringValue(this.getName()));
        instrumentedMsgs.add(value);
        instrumentation.commit();

        this.networkManager.send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.PREPARED.toString(), this.instrumentation.getClock().getValue()));

    }

    /**
     * @TLA-action RMRcvCommitMsg(r)
     */
    protected void commit() throws TraceProducerException {
        // Simulate some task that take some time
        long d = 150 + Helper.next(2000);
        //System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(), d);
        try {Thread.sleep(d); } catch (InterruptedException ex) {}
        this.setState(ResourceManagerState.COMMITTED);
        // Commit events
        instrumentation.commit();
        // Shutdown process
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
        // Commit events
        instrumentation.commit();
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
