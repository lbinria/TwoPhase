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

    private final static int PROBABILITY_TO_ABORT = 2;
    private static final int MAX_TASK_DURATION = 100;

    // Transaction manager (to send message)
    private final String transactionManagerName;
    // Current state
    private ResourceManagerState state;
    private final int taskDuration;

    // tracing
    private final VirtualField specMessages;
    private final VirtualField specState;

    /**
     * Construct a resource manager
     * 
     * @param NetworkManager         Network support (for send/receive messages)
     * @param name                   Resource manager name
     * @param transactionManagerName Attached transaction manager name
     * @param taskDuration           Duration of underlying task
     * @param spec                   Trace instrumentation
     */
    public ResourceManager(NetworkManager networkManager, String name, String transactionManagerName,
            int taskDuration, TLATracer spec) {
        super(name, networkManager, spec);
        this.transactionManagerName = transactionManagerName;
        this.state = ResourceManagerState.WORKING;
        if (taskDuration == -1) {
            this.taskDuration = Helper.next(MAX_TASK_DURATION);
        } else {
            this.taskDuration = taskDuration;
        }
        // prepare tracing
        this.specMessages = spec.getVariable("msgs");
        this.specState = spec.getVariable("rmState").getField(getName());

        System.out.println("RM " + name + " WORKING - " + taskDuration + " ms");
    }

    @Override
    public void run() throws IOException {
        // possible crash of the RM
        int possibleAbort = Helper.next(PROBABILITY_TO_ABORT);
        if (possibleAbort == 1) {
            System.out.println("RM " + this.getName() + " ABORT ");
            this.shutdown();
            return;
        }
        // work
        working();
        // Continuously send prepared while not committed
        do {
            // send Prepared message
            this.sendPrepared();
            // block on receiving message until timeout, send again if timeout
            try {
                Message message = networkManager.syncReceive(this.getName(), this.taskDuration * 2);
                this.receive(message);
            } catch (TimeOutException e) {
                System.out.println("RM " + this.getName() + " received TIMEOUT ");
            }
        } while (!this.isShutdown());
    }

    private void working() {
        // Simulate task
        try {
            Thread.sleep(this.taskDuration);
        } catch (InterruptedException ex) {
        }
    }

    private void sendPrepared() throws IOException {
        // Trace optimization (specify event name to reduce state space)
        final String eventName;
        if (this.state != ResourceManagerState.PREPARED) {
            eventName = "RMPrepare";
        } else {
            eventName = "Stuttering";
        }

        spec.startLog(); // prepare to log event
        this.state = ResourceManagerState.PREPARED;
        this.specState.set(state.toString().toLowerCase(Locale.ROOT));
        // spec.log(eventName);
        this.networkManager.send(new Message(
                this.getName(), transactionManagerName, TwoPhaseMessage.Prepared.toString(), 0));

        // spec.notifyChange("msgs", "Add", List.of(), List.of(Map.of("type",
        // TwoPhaseMessage.Prepared.toString(), "rm", getName())));
        specMessages.add(Map.of("type", TwoPhaseMessage.Prepared.toString(), "rm", getName())); // add Add op for
                                                                                                // Messages to the trace
        spec.endLog(eventName); // log event

        System.out.println("RM " + this.getName() + " send " + TwoPhaseMessage.Prepared);
    }

    private void receive(Message message) throws IOException {
        if (message.getContent().equals(TwoPhaseMessage.Commit.toString())) {
            spec.startLog(); // prepare to log event
            this.state = ResourceManagerState.COMMITTED;
            this.specState.set(state.toString().toLowerCase(Locale.ROOT));
            spec.endLog("RMRcvCommitMsg");
            this.shutdown();
        } else if (message.getContent().equals(TwoPhaseMessage.Abort.toString())) {
            spec.startLog(); // prepare to log event
            this.state = ResourceManagerState.ABORTED;
            this.specState.set(state.toString().toLowerCase(Locale.ROOT));
            spec.endLog("RMRcvAbortMsg");
            this.shutdown();
        }

        System.out.println("RM " + this.getName() +
                " received: " + message.getContent() + " from " + message.getFrom());
    }
}
