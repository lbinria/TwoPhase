package org.lbee.twophase;

import java.io.*;
import java.net.Socket;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
        super.run();

        // Waiting for all resource manager registered
        if (resourceManagers.size() < config.nResourceManager)
            return;

        // Do just once
        if (!isAllRegistered) {
            System.out.println("All expected resource managers are registered.");
            // TODO do that with configuration file of the system
            String strResourceManagers = this.resourceManagers.stream().map(r -> "\"" + r + "\"").collect(Collectors.joining(", "));
            String rmValue = "{" + strResourceManagers + "}";
            TLAConfigTemplate TLAconfigTemplate = new TLAConfigTemplate(Map.of("RM", rmValue));
            // TODO modify hard-coded path
            TLAconfigTemplate.generate("TwoPhaseTrace.template.cfg");
            isAllRegistered = true;
        }

        // TODO commit can be happen at the same time as abort => error
        if (checkCommit())
            this.commit();

        if (checkTimeout())
            this.abort();

    }

    protected void receive(Message message) throws IOException {
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

        System.out.println(TwoPhaseMessage.COMMIT + ".");
        // Log event (hard-coded for now)
        logger.log(this, "msgs", TwoPhaseMessage.COMMIT.toString());
        logger.commit();

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

        System.out.println(TwoPhaseMessage.ABORT + ".");
        // Log event (hard-coded for now)
        logger.log(this, "msgs", TwoPhaseMessage.ABORT.toString());
        logger.commit();

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

        // Log event (hard-coded for now)
        logger.log(this, "tmPrepared", sender);
        logger.commit();
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
