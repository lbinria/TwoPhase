package org.lbee.twophase;

import java.io.*;
import java.net.Socket;
import java.util.HashSet;
import java.util.Optional;

public class TransactionManager2 extends NetworkProcess2 {

    // Logger
    private final TLALogger logger;
    // Config
    private final TransactionManager2.TransactionManagerConfiguration config;

    // Resource manager linked to TM
    private final HashSet<String> resourceManagers;
    // Resource manager prepared to commit
    private final HashSet<String> preparedResourceManagers;

    private boolean isAllRegistered = false;

    @Override
    public String getName() {
        return "TM";
    }

    public TransactionManager2(Socket socket, TransactionManagerConfiguration config) throws IOException {
        super(socket);

        resourceManagers = new HashSet<>();
        preparedResourceManagers = new HashSet<>();
        logger = new TLALogger();
        this.config = config;
    }

    @Override
    public void run() throws IOException {

        // Check eventual received message
        checkMessage();

        // Waiting for all resource manager registered
        if (resourceManagers.size() < config.nResourceManager)
            return;

        if (!isAllRegistered) {
            System.out.println("All expected resource managers are registered.");
            isAllRegistered = true;
        }

        // TODO commit can be happen at the same time as abort => error
        if (checkCommit())
            this.commit();

        if (checkTimeout())
            this.abort();

    }

    protected void checkMessage() throws IOException {
        Message message = receive();

        if (message == null)
            return;

        // Sync process clock
        this.logicalClock.sync(message.getSenderClock());

        System.out.printf("%s - %s receive message: `%s`...\n", this.logicalClock, this.getName(), message.getContent());
        switch (message.getContent()) {
            case "Register" -> this.receivedRegister(message.getFrom());
            case "Prepared" -> this.receivePrepared(message.getFrom());
            /* Nothing to do */
            default -> {}
        }
    }

    protected void receivedRegister(String resourceManagerName) {
        System.out.printf("Register a new resource manager: %s.\n", resourceManagerName);
        this.resourceManagers.add(resourceManagerName);
    }

    protected boolean checkCommit()  {
        return this.preparedResourceManagers.containsAll(this.resourceManagers) || this.config.commitAnyway;
    }

    protected boolean checkTimeout() {
        return this.logicalClock.getValue() >= this.config.timeout;
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        for (String rmName : resourceManagers)
            this.send(new Message(this.getName(), rmName, TwoPhaseMessage.COMMIT.toString(), this.logicalClock.getValue()));

        System.out.println("Commit.");
        this.shutdown();
    }

    /**
     * @TLAAction TMAbort
     */
    public void abort() throws IOException {
        System.out.printf("%s timeout reach.\n", this.getName());

        for (String rmName : resourceManagers) {
            Message m = new Message(this.getName(), rmName, TwoPhaseMessage.ABORT.toString(), this.logicalClock.getValue());
            this.send(m);
        }

        System.out.println("Abort.");
        this.shutdown();
    }

    /**
     * @TLAAction TMRcvPrepared(r)
     */
    public void receivePrepared(String sender) {
        /* Search receive prepared resource manager in resource manager set */
        Optional<String> optionalResourceManager = resourceManagers.stream().filter(rmName -> rmName.equals(sender)).findFirst();
        /* If it doesn't exist do nothing */
        if (optionalResourceManager.isEmpty())
            return;

        /* Add prepared resource manager to prepared set */
        preparedResourceManagers.add(optionalResourceManager.get());
    }

    /**
     * Configuration of a resource manager
     * @param timeout Is resource manager should fail, invoke an unknown exception
     * @param commitAnyway Commit even if some RM are not prepared (introduce error in implementation)
     */
    record TransactionManagerConfiguration(int nResourceManager, int timeout, boolean commitAnyway) {
        @Override
        public String toString() {
            return "TransactionManagerConfiguration{" +
                    "timeout=" + timeout +
                    '}';
        }
    }

}
