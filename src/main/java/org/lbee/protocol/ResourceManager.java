package org.lbee.protocol;

import org.lbee.helpers.Helper;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;
import org.lbee.network.NetworkManager;
import org.lbee.network.TimeOutException;
import java.io.IOException;
import java.util.Locale;
import java.util.Map;

public class ResourceManager extends Manager {

    /**
     * Possible states of resource manager
     */
    enum ResourceManagerState {
        WORKING,
        PREPARED,
        COMMITTED,
        ABORTED
    }

    private final static int PROBABILITY_TO_ABORT = 100;
    private static final int MAX_TASK_DURATION = 100;

    // Transaction manager (to send message)
    private final String transactionManagerName;
    // Current state
    private ResourceManagerState state;
    private final int taskDuration;

    // tracing
    private final VirtualField traceMessages;
    private final VirtualField traceState;

    /**
     * Construct a resource manager
     * 
     * @param NetworkManager         Network support (for send/receive messages)
     * @param name                   Resource manager name
     * @param transactionManagerName Attached transaction manager name
     * @param taskDuration           Duration of underlying task
     * @param tracer                 Trace instrumentation
     */
    public ResourceManager(NetworkManager networkManager, String name, String transactionManagerName,
            int taskDuration, TLATracer tracer) {
        super(name, networkManager, tracer);
        this.transactionManagerName = transactionManagerName;
        this.state = ResourceManagerState.WORKING;
        if (taskDuration == -1) {
            this.taskDuration = Helper.next(MAX_TASK_DURATION);
        } else {
            this.taskDuration = taskDuration;
        }
        // prepare tracing
        this.traceMessages = tracer.getVariableTracer("msgs");
        this.traceState = tracer.getVariableTracer("rmState").getField(this.name);

        System.out.println("RM " + name + " WORKING - " + taskDuration + " ms");
    }

    @Override
    public void run() throws IOException {
        boolean done = false;
        // Simulate a crash of the RM
        int possibleAbort = Helper.next(PROBABILITY_TO_ABORT);
        if (possibleAbort == 1) {
            System.out.println("RM " + this.name + " ABORT ");
            done = true;
            return;
        }
        // work
        working();
        // Continuously send prepared while not committed
        while (!done) {
            // send Prepared message
            this.sendPrepared();
            // block on receiving message until timeout, send again if timeout
            try {
                Message message = networkManager.receive(this.name, this.taskDuration * 2);
                this.handleMessage(message);
                done = true;
            } catch (TimeOutException e) {
                System.out.println("RM " + this.name + " received TIMEOUT ");
            }
        }
        System.out.println("-- RM " + this.name + " shutdown");
    }

    private void working() {
        // Simulate task
        try {
            Thread.sleep(this.taskDuration);
        } catch (InterruptedException ex) {
        }
    }

    private void handleMessage(Message message) throws IOException {
        if (message.getContent().equals(TwoPhaseMessage.Commit.toString())) {
            this.state = ResourceManagerState.COMMITTED;
            this.traceState.set(this.state.toString().toLowerCase(Locale.ROOT));
            tracer.log("RMRcvCommitMsg", new Object[] { this.name });
            // tracer.log();
            // tracer.log("RMRcvCommitMsg");
        } else if (message.getContent().equals(TwoPhaseMessage.Abort.toString())) {
            this.state = ResourceManagerState.ABORTED;
            this.traceState.set(this.state.toString().toLowerCase(Locale.ROOT));
            tracer.log("RMRcvAbortMsg");
        }

        System.out.println("RM " + this.name +
                " received: " + message.getContent() + " from " + message.getFrom());
    }

    private void sendPrepared() throws IOException {
        // Trace optimization (specify event name to reduce state space)
        final String eventName;
        if (this.state != ResourceManagerState.PREPARED) {
            eventName = "RMPrepare";
        } else {
            eventName = "Stuttering";
        }

        this.state = ResourceManagerState.PREPARED;
        this.traceState.set(state.toString().toLowerCase(Locale.ROOT));
        // spec.notifyChange("msgs", "Add", List.of(), List.of(Map.of("type",
        // TwoPhaseMessage.Prepared.toString(), "rm", getName())));
        traceMessages.add(Map.of("type", TwoPhaseMessage.Prepared.toString(), "rm", this.name)); // add Add op for
        // should log before the message is sent // Messages to the trace
        tracer.log(eventName);

        this.networkManager.send(new Message(
                this.name, transactionManagerName, TwoPhaseMessage.Prepared.toString(), 0));

        System.out.println("RM " + this.name + " sent " + TwoPhaseMessage.Prepared);
    }

}
