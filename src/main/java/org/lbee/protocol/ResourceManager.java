package org.lbee.protocol;

import org.lbee.helpers.Helper;
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
    private ResourceManagerState state = ResourceManagerState.WORKING;
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
     * @throws IOException Throws when errors occur on clock 
     */
    public ResourceManager(NetworkManager networkManager, String name, String transactionManagerName,
            int taskDuration) throws IOException {
        super(name, networkManager);
        this.transactionManagerName = transactionManagerName;
        if (taskDuration == -1) {
            this.taskDuration = Helper.next(500);
        } else {
            this.taskDuration = taskDuration;
        }
        specState = spec.getVariable("rmState").getField(getName());
        System.out.println("RM " + name + " - " + taskDuration + " ms");
    }

    // private void reset() throws IOException {
    // setState(ResourceManagerState.WORKING);
    // spec.commitChanges("RMReset");
    // }

    /**
     * Set state of manager
     * 
     * @param state New manager state
     */
    private void setState(ResourceManagerState state) {
        // Change state
        this.state = state;
        specState.set(state.toString().toLowerCase(Locale.ROOT));
    }

    /**
     * Get state of manager
     * 
     * @return Current state of manager
     */
    public ResourceManagerState getState() {
        return this.state;
    }

    @Override
    public void run() throws IOException {
        // If working simulate task, and then prepare
        if (this.getState() == ResourceManagerState.WORKING) {
            try {
                Thread.sleep(this.taskDuration);
            } catch (InterruptedException ex) {
            }
            // this.prepare();
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

    private void receive(Message message) throws IOException {
        /* Eventually commit */
        if (message.getContent().equals(TwoPhaseMessage.Commit.toString())) {
            this.commit();
            System.out.println("RM " + this.getName() + " received COMMIT");
        } else {
            System.out.println("RM " + this.getName() + "  received OTHER");
        }
        /* Nothing else to do */
    }

    private void sendPrepared() throws IOException {
        this.setState(ResourceManagerState.PREPARED);
        specMessages.add(Map.of("type", TwoPhaseMessage.Prepared.toString(), "rm", getName()));
        spec.commitChanges();
        this.networkManager
                .send(new Message(this.getName(), transactionManagerName, TwoPhaseMessage.Prepared.toString(), 0));
        System.out.println("RM " + this.getName() + "  send PREPARED");
    }

    /**
     * @TLA-action RMRcvCommitMsg(r)
     */
    protected void commit() throws IOException {
        // Simulate some task that take some time
        long d = 150 + Helper.next(1000);
        // System.out.printf("COMMIT TASK DURATION of %s : %s ms.\n", this.getName(),
        // d);
        try {
            Thread.sleep(d);
        } catch (InterruptedException ex) {
        }
        this.setState(ResourceManagerState.COMMITTED);
        spec.commitChanges("RMRcvCommitMsg");
        // Shutdown process
        this.shutdown();
    }

    /**
     * Check whether the manager is in working state
     * 
     * @return True if manager is in working state, else false
     */
    // private boolean isWorking() {
    // return this.getState() == ResourceManagerState.WORKING;
    // }

    /**
     * Check whether the manager is in committed state
     * 
     * @return True if manager is in committed state, else false
     */
    // private boolean isCommitted() {
    // return this.getState() == ResourceManagerState.COMMITTED;
    // }

}
