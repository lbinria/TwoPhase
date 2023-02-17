package org.lbee.twophase;

import javax.swing.text.html.Option;
import java.util.HashSet;
import java.util.Optional;
import java.util.concurrent.Callable;

/**
 * Simulate a transaction manager node
 */
public class TransactionManager implements Callable<Void>, TLANamedProcess, NetworkProcess {

    // Logger
    private final TLALogger logger;
    // Config
    private final TransactionManagerConfiguration config;
    // TM name
    private final String name;
    private final NetworkMock networkMock;
    // Local clock
    //private long clock;
    // Resource manager linked to TM
    private final HashSet<ResourceManager> resourceManagers;
    // Resource manager prepared to commit
    private final HashSet<ResourceManager> preparedResourceManagers;
    // Start time (for timeout)
    private final long start;

    private LogicalClock logicalClock;

    @Override
    public String getName() {
        return this.name;
    }


    public TransactionManager(NetworkMock networkMock, TransactionManagerConfiguration config) {
        this.networkMock = networkMock;
        this.name = "TM";
        this.config = config;
        this.resourceManagers = new HashSet<>();
        this.start = System.currentTimeMillis();
        this.logger = new TLALogger();
        this.preparedResourceManagers = new HashSet<>();
        this.logicalClock = new LogicalClock();
    }

    @Override
    public Void call() throws Exception {

        // Blocks task until transaction manager commit or abort
        while (!(this.checkCommit() || this.checkTimeout())) {
            //clock++;
            // Receive messages
            this.receive();
        }

        /* Only commit if all resource managers were prepared */
        if (this.checkCommit())
            this.commit();
        /* Only abort if timeout was reached */
        else if (this.checkTimeout())
            this.abort();

        // Nothing should never happen
        return null;
    }

    public void addResourceManager(ResourceManager resourceManager) {
        this.resourceManagers.add(resourceManager);
    }

    /**
     * @TLA-action TMCommit
     */
    private void commit() {
        this.send(new Message(this.getName(), TwoPhaseMessage.COMMIT.toString(), this.logicalClock.getValue()));
    }

    /**
     * @TLA-action TMAbort
     */
    public void abort() {
        System.out.printf("%s timeout reach.\n", this.getName());
        this.send(new Message(this.getName(), TwoPhaseMessage.ABORT.toString(), this.logicalClock.getValue()));
    }

    /**
     * @TLA-action TMRcvPrepared(r)
     */
    public void receivePrepared(String sender) {
        /* Search receive prepared resource manager in resource manager set */
        Optional<ResourceManager> optionalResourceManager = resourceManagers.stream().filter(rm -> rm.getName().equals(sender)).findFirst();
        /* If it doesn't exist do nothing */
        if (optionalResourceManager.isEmpty())
            return;

        /* Add prepared resource manager to prepared set */
        preparedResourceManagers.add(optionalResourceManager.get());
    }

    /**
     * @param message
     */
    @Override
    public void send(Message message) {
        // System.out.printf("%s - %s send message: `%s`...\n", this.clock, this.getName(), message.content());
        // Send message to all resource managers
        for (ResourceManager rm : this.resourceManagers) {
            System.out.printf("%s - %s send message: `%s` to %s...\n", this.logicalClock, this.getName(), message.content(), rm.getName());
            // Simulate a delay to send from 0 to 200 ms
            try { Thread.sleep(Helper.next(200)); } catch (InterruptedException ex) {}
            networkMock.put(rm.getName(), message);
        }
    }

    @Override
    public void receive() throws InterruptedException {
        Message message = networkMock.take(this.getName());

        if (message == null)
            return;

        // Sync process clock
        this.logicalClock.sync(message.senderClock());

        System.out.printf("%s - %s receive message: `%s`...\n", this.logicalClock, this.getName(), message.content());
        switch (message.content()) {
            case "Prepared" -> this.receivePrepared(message.sender());
            /* Nothing to do */
            default -> {}
        }
    }

    protected boolean checkCommit()  {
        return this.preparedResourceManagers.containsAll(this.resourceManagers) || this.config.commitAnyway;
    }

    protected boolean checkTimeout() {
        return System.currentTimeMillis() - this.start >= this.config.timeout;
    }

    /**
     * Configuration of a resource manager
     * @param timeout Is resource manager should fail, invoke an unknown exception
     * @param commitAnyway Commit even if some RM are not prepared (introduce error in implementation)
     */
    record TransactionManagerConfiguration(int timeout, boolean commitAnyway) {
        @Override
        public String toString() {
            return "TransactionManagerConfiguration{" +
                    "timeout=" + timeout +
                    '}';
        }
    }

}
