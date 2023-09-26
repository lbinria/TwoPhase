package org.lbee.protocol;

import org.lbee.helpers.Helper;
import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
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
            int taskDuration, BehaviorRecorder spec) {
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

    /**
     * Set state of manager
     * 
     * @param state New manager state
     */
    private void setState(ResourceManagerState state) {
        this.state = state;
        // Tracing
        this.specState.set(state.toString().toLowerCase(Locale.ROOT));
    }

    @Override
    public void run() throws IOException {
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
        this.setState(ResourceManagerState.PREPARED);
        // Tracing
        specMessages.add(Map.of("type", TwoPhaseMessage.Prepared.toString(), "rm", getName()));
        spec.commitChanges();
        this.networkManager
                .send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.Prepared.toString(), 0));

        System.out.println("RM " + this.getName() + " send " + TwoPhaseMessage.Prepared);
    }

    private void receive(Message message) throws IOException {
        if (message.getContent().equals(TwoPhaseMessage.Commit.toString())) {
            this.setState(ResourceManagerState.COMMITTED);
            // Tracing
            spec.commitChanges("RMRcvCommitMsg");

            this.shutdown();
        } else if (message.getContent().equals(TwoPhaseMessage.Abort.toString())) {
            this.setState(ResourceManagerState.ABORTED);
            // Tracing
            spec.commitChanges("RMRcvAbortMsg");
            
            this.shutdown();
        }

        System.out.println("RM " + this.getName() + " received: " + message.getContent() + " from " + message.getFrom());
    }
}
