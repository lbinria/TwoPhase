package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.SharedClock;
import org.lbee.models.Message;
import org.lbee.models.TwoPhaseMessage;

import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class TransactionManager extends Manager implements NamedClient {

    // Config
    private final TransactionManager.TransactionManagerConfiguration config;
    // Resource manager linked to TM
    private final HashSet<String> resourceManagers;
    // Resource manager prepared to commit
    private final HashSet<String> preparedResourceManagers;

    private boolean isAllRegistered = false;

    private final VirtualField specTmPrepared;

    public TransactionManager(Socket socket, TransactionManagerConfiguration config) throws IOException {
        super("TM", socket);

        resourceManagers = new HashSet<>();
        preparedResourceManagers = new HashSet<>();
        this.config = config;

        this.specTmPrepared = spec.getVariable("tmPrepared");
    }

    private void reset() {
        resourceManagers.clear();
        preparedResourceManagers.clear();
        specTmPrepared.clear();
        spec.commitChanges("TMReset");
    }

    @Override
    public void run() throws IOException, TraceProducerException {
        // Check eventual received message
        super.run();

        // Waiting for all resource manager registered
        if (resourceManagers.size() < config.nResourceManager)
            return;

        // Do just once
        if (!isAllRegistered) {
            System.out.println("All expected resource managers are registered.");
            String strResourceManagers = this.resourceManagers.stream().map(r -> "\"" + r + "\"").collect(Collectors.joining(", "));
            String rmValue = "{" + strResourceManagers + "}";
            // TODO here write to trace file
            isAllRegistered = true;
        }

        // TODO commit can be happen at the same time as abort => error
        if (checkCommit())
            this.commit();

        if (checkTimeout())
            this.abort();

    }

    protected void receive(Message message) throws IOException, TraceProducerException {
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

        //return this.instrumentation.getClock().getValue() >= this.config.timeout;
        return false;
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        // Notify
        specMessages.add(Map.of("type", "Commit"));
        spec.commitChanges("TMCommit");

        for (String rmName : resourceManagers)
            this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.COMMIT.toString(), 0));

        // Display message
        System.out.println(TwoPhaseMessage.COMMIT + ".");

        // Shutdown
        this.shutdown();
    }

    /**
     * @TLAAction TMAbort
     */
    public void abort() throws IOException, TraceProducerException {
        System.out.printf("%s timeout reach.\n", this.getName());

        // Notify
        specMessages.add(Map.of("type", "Abort"));
        spec.commitChanges("TMAbort");

        for (String rmName : resourceManagers) {
            Message m = new Message(this.getName(), rmName, TwoPhaseMessage.ABORT.toString(), 0);
            this.networkManager.send(m);
        }

        System.out.println(TwoPhaseMessage.ABORT + ".");

        this.reset();
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
        String rmName = optionalResourceManager.get();
        preparedResourceManagers.add(rmName);
//        specTmPrepared.add(rmName);
        spec.commitChanges("TMRcvPrepared");
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
