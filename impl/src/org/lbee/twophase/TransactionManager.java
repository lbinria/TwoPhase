package org.lbee.twophase;

import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.tla.value.TLARecordValue;
import org.lbee.instrumentation.tla.variable.TLASetVariable;
import org.lbee.instrumentation.tla.value.TLAStringValue;
import org.lbee.instrumentation.tla.variable.TLAStringVariable;
import org.lbee.twophase.models.Message;
import org.lbee.twophase.models.TwoPhaseMessage;

import java.io.IOException;
import java.net.Socket;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class TransactionManager extends Manager implements NamedClient {

    // Instrumented values
    private final TLAStringVariable instrumentedState;
    private final TLASetVariable<TLARecordValue> instrumentedMsgs;
    private final TLASetVariable<TLAStringValue> instrumentedPreparedResourceManagers;

    // Config
    private final TransactionManager.TransactionManagerConfiguration config;
    // Resource manager linked to TM
    private final HashSet<String> resourceManagers;
    // Resource manager prepared to commit
    private final HashSet<String> preparedResourceManagers;

    private boolean isAllRegistered = false;

    @Override
    public String getName() {
        return "TM";
    }

    public TransactionManager(Socket socket, TransactionManagerConfiguration config) throws IOException {
        super(socket);

        resourceManagers = new HashSet<>();
        preparedResourceManagers = new HashSet<>();
        this.config = config;

        // TODO Here can be read from a configuration file
        this.instrumentedState = this.instrumentation.add("tmState", TLAStringVariable::new);
        this.instrumentedMsgs = this.instrumentation.add("msgs", TLASetVariable<TLARecordValue>::new);
        this.instrumentedPreparedResourceManagers = this.instrumentation.add("tmPrepared", TLASetVariable<TLAStringValue>::new);
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
            // TODO do that with configuration file of the system
            String strResourceManagers = this.resourceManagers.stream().map(r -> "\"" + r + "\"").collect(Collectors.joining(", "));
            String rmValue = "{" + strResourceManagers + "}";
            TLAConfigTemplate TLAconfigTemplate = new TLAConfigTemplate(Map.of("RM", rmValue));
            // TODO modify hard-coded path
            TLAconfigTemplate.generate("TwoPhaseTrace_v5a.template.cfg");
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
        return this.instrumentation.getClock().getValue() >= this.config.timeout;
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException, TraceProducerException {
        for (String rmName : resourceManagers)
            this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.COMMIT.toString(), this.instrumentation.getClock().getValue()));

        // Display message
        System.out.println(TwoPhaseMessage.COMMIT + ".");

        // Log event (hard-coded for now)
        TLAMsgs value = new TLAMsgs(new TLAStringValue(TwoPhaseMessage.COMMIT.toString()));
        this.instrumentedMsgs.add(value);
        this.instrumentedState.set(new TLAStringValue("bob"));
        this.instrumentedState.set(new TLAStringValue("done"));
        this.instrumentation.commit();

        // Shutdown
        this.shutdown();
    }

    /**
     * @TLAAction TMAbort
     */
    public void abort() throws IOException, TraceProducerException {
        System.out.printf("%s timeout reach.\n", this.getName());

        for (String rmName : resourceManagers) {
            Message m = new Message(this.getName(), rmName, TwoPhaseMessage.ABORT.toString(), this.instrumentation.getClock().getValue());
            this.networkManager.send(m);
        }

        System.out.println(TwoPhaseMessage.ABORT + ".");
        // Log event (hard-coded for now)
        TLAMsgs value = new TLAMsgs(new TLAStringValue(TwoPhaseMessage.ABORT.toString()));
        this.instrumentedMsgs.add(value);

        instrumentation.commit();

        this.shutdown();

    }

    /**
     * @TLAAction TMRcvPrepared(r)
     */
    public void receivePrepared(String sender) throws TraceProducerException {
        /* Search receive prepared resource manager in resource manager set */
        Optional<String> optionalResourceManager = resourceManagers.stream().filter(rmName -> rmName.equals(sender)).findFirst();
        /* If it doesn't exist do nothing */
        if (optionalResourceManager.isEmpty())
            return;

        /* Add prepared resource manager to prepared set */
        preparedResourceManagers.add(optionalResourceManager.get());

        // Log event (hard-coded for now)
        this.instrumentedPreparedResourceManagers.add(new TLAStringValue(sender));
        instrumentation.commit();
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
