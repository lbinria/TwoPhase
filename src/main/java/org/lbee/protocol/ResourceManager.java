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
        COMMITTED
    }

    // Transaction manager (to send message)
    private final String transactionManagerName;
    // Current state
    private ResourceManagerState state;
    private final int taskDuration;

    // tracing
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
            this.taskDuration = Helper.next(500);
        } else {
            this.taskDuration = taskDuration;
        }
        specState = spec.getVariable("rmState").getField(getName());
        System.out.println("RM " + name + " - " + taskDuration + " ms");
    }

    /**
     * Set state of manager
     * 
     * @param state New manager state
     */
    private void setState(ResourceManagerState state) {
        this.state = state;
        // Tracing
        specState.set(state.toString().toLowerCase(Locale.ROOT));
    }

    @Override
    public void run() throws IOException {
        // Simulate task, and then prepare
        try {
            Thread.sleep(this.taskDuration);
        } catch (InterruptedException ex) {
        }
        // Continuously send prepared while not committed
        do {
            // send Prepared message
            this.sendPrepared();
            // block on receiving message until timeout
            // -> send again if timeout
            try {
                Message message = networkManager.syncReceive(this.getName(), -1);
                this.receive(message);
            } catch (TimeOutException e) {
                System.out.println("RM " + this.getName() + " received TIMEOUT ");
            }
        } while (!this.isShutdown());
    }

    private void sendPrepared() throws IOException {
        this.setState(ResourceManagerState.PREPARED);
        this.networkManager
                .send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.Prepared.toString(), 0));
        System.out.println("RM " + this.getName() + "  send PREPARED");
        // Tracing
        specMessages.add(Map.of("type", TwoPhaseMessage.Prepared.toString(), "rm", getName()));
        spec.commitChanges();
    }

    private void receive(Message message) throws IOException {
        if (message.getContent().equals(TwoPhaseMessage.Commit.toString())) {
            this.setState(ResourceManagerState.COMMITTED);
            System.out.println("RM " + this.getName() + " received COMMIT");
            // Tracing
            spec.commitChanges("RMRcvCommitMsg");
            this.shutdown();
        } else {
            System.out.println("RM " + this.getName() + "  received OTHER");
        }
    }
}
