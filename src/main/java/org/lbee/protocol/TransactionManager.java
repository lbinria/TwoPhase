package org.lbee.protocol;

import org.lbee.instrumentation.VirtualField;
import org.lbee.network.NetworkManager;
import org.lbee.network.TimeOutException;

import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
// import java.util.stream.Collectors;

public class TransactionManager extends Manager {
    // Resource managers managed by TM
    private final HashSet<String> resourceManagers;
    // Number of resource manager prepared to commit
    private int nbPrepared;
    // private boolean isAllRegistered = false;

    private final VirtualField specTmPrepared;

    public TransactionManager(NetworkManager networkManager, List<String> resourceManagerNames)
            throws IOException {
        super("tm", networkManager);

        this.resourceManagers = new HashSet<>(resourceManagerNames);
        // Even if nbPrepared doesn't neccesarily reflect the number of prepared RM when
        // the commit decision was taken, increasing the commit duration might lead to a
        // valid trace because the last RM (not counted by nbPrepared when the commit
        // decision was taken) has time to send its Prepared message before TM send the
        // commit message
        this.nbPrepared = 0;
        this.specTmPrepared = spec.getVariable("tmPrepared");
    }

    @Override
    public void run() throws IOException {
        do {
            // block on receiving message until timeout
            // -> retry if timeout
            boolean received = false;
            do {
                try {
                    Message message = networkManager.syncReceive(this.getName(), 10);
                    this.receive(message);
                    received = true;
                } catch (TimeOutException e) {
                    System.out.println("TM receive TIMEOUT");
                }
            } while (!received);

            if (checkCommit()) {
                System.out.println("TM check commit OK");
                this.commit();
            }
        } while (!this.isShutdown());
    }

    protected void receive(Message message) throws IOException {
        System.out.println("TM received: " + message.getContent());
        if (message.getContent().equals(TwoPhaseMessage.Prepared.toString())) {
            this.receivePrepared(message.getFrom());
        }
    }

    protected boolean checkCommit() {
        System.out.println("TM nbPrepared = " + nbPrepared);
        System.out.println("TM rms = " + this.resourceManagers);
        return this.nbPrepared >= this.resourceManagers.size();
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        System.out.println("TM sends Commits");
        // Notify
        specMessages.add(Map.of("type", TwoPhaseMessage.Commit.toString()));
        spec.commitChanges("TMCommit");
        // sends Commits to all RM
        for (String rmName : resourceManagers) {
            this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.Commit.toString(), 0));
        }
        // Shutdown
        this.shutdown();
    }

    /**
     * @TLAAction TMRcvPrepared(r)
     */
    public void receivePrepared(String sender) throws IOException {
        /* Search receive prepared resource manager in resource manager set */
        Optional<String> optionalResourceManager = resourceManagers.stream().filter(rmName -> rmName.equals(sender))
                .findFirst();
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
