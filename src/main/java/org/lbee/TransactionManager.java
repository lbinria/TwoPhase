package org.lbee;

import org.lbee.instrumentation.VirtualField;
import org.lbee.models.Message;
import org.lbee.models.TwoPhaseMessage;

import java.io.IOException;
import java.net.Socket;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class TransactionManager extends Manager implements NamedClient {

    // Config
    private final TransactionManagerConfiguration config;
    // Resource manager linked to TM
    private final HashSet<String> resourceManagers;

    // Number of resource manager prepared to commit
    private int nbPrepared;

    private boolean isAllRegistered = false;

    private final VirtualField specTmPrepared;

    private final int commitDuration;
    private long lastTick;

    public TransactionManager(Socket socket, TransactionManagerConfiguration config) throws IOException {
        super("TM", socket);

        resourceManagers = new HashSet<>();
        // Note: invert comment to introduce bug
//        nbPrepared = 0;
        // Even if nbPrepared is false, increase the commit duration led to a valid trace
        // Because the last RM have time to send is Prepared message before TM propose to commit
        nbPrepared = 0;
        commitDuration = 0;

        this.config = config;

        this.specTmPrepared = spec.getVariable("tmPrepared");
    }

    @Override
    public void run() throws IOException {
        // Check eventual received message
        super.run();

        // Waiting for all resource manager registered
        if (resourceManagers.size() < config.nResourceManager())
            return;

        // Do just once
        if (!isAllRegistered) {
            System.out.println("All expected resource managers are registered.");
            String strResourceManagers = this.resourceManagers.stream().map(r -> "\"" + r + "\"").collect(Collectors.joining(", "));
            String rmValue = "{" + strResourceManagers + "}";
            isAllRegistered = true;
        }

        if (checkCommit()) {
            if (lastTick == 0)
                lastTick = System.currentTimeMillis();

            // Wait 1s
            if (System.currentTimeMillis() - lastTick >= commitDuration)
                this.commit();
        }
    }

    protected void receive(Message message) throws IOException {
        if (message.getContent().equals(TwoPhaseMessage.Register.toString())) {
            this.receivedRegister(message.getFrom());
        } else if (message.getContent().equals(TwoPhaseMessage.Prepared.toString())) {
            this.receivePrepared(message.getFrom());
        }
    }

    protected void receivedRegister(String resourceManagerName) {
        System.out.printf("Register a new resource manager: %s.\n", resourceManagerName);
        this.resourceManagers.add(resourceManagerName);
    }

    protected boolean checkCommit()  {
        return this.nbPrepared >= this.resourceManagers.size();
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        // Notify
        specMessages.add(Map.of("type", TwoPhaseMessage.Commit.toString()));
        spec.commitChanges("TMCommit");

        for (String rmName : resourceManagers)
            this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.Commit.toString(), 0));

        // Display message
        System.out.println(TwoPhaseMessage.Commit + ".");

        // Shutdown
        this.shutdown();
    }

    /**
     * @TLAAction TMRcvPrepared(r)
     */
    public void receivePrepared(String sender) throws IOException {
        /* Search receive prepared resource manager in resource manager set */
        Optional<String> optionalResourceManager = resourceManagers.stream().filter(rmName -> rmName.equals(sender)).findFirst();
        /* If it doesn't exist, do nothing */
        if (optionalResourceManager.isEmpty())
            return;

        /* Add prepared resource manager to prepared set */
        String rmName = optionalResourceManager.get();
        nbPrepared++;
        specTmPrepared.add(rmName);
        spec.commitChanges("TMRcvPrepared");
    }



}
