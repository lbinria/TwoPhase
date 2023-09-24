package org.lbee.protocol;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.network.NetworkManager;
import org.lbee.network.TimeOutException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class TransactionManager extends Manager {
    // Resource managers managed by TM (as specified in the configuration)
    private final Set<String> resourceManagers;
    // Number of resource managers prepared to commit
    private Collection<String> preparedRMs;

    private final VirtualField specTmPrepared;

    public TransactionManager(NetworkManager networkManager, String name, List<String> resourceManagerNames,
            BehaviorRecorder spec) {
        super(name, networkManager, spec);

        this.resourceManagers = new HashSet<>(resourceManagerNames);
        // Even if preparedRMs.size doesn't neccesarily reflect the number of prepared
        // RM when
        // the commit decision was taken, increasing the commit duration might lead to a
        // valid trace because the last RM (not counted by nbPrepared when the commit
        // decision was taken) has time to send its Prepared message before TM send the
        // commit message
        this.preparedRMs = new ArrayList<>();
        // this.preparedRMs = new HashSet<>();
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
                    Message message = networkManager.syncReceive(this.getName(), 100);
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
        System.out.println("TM received: " + message.getContent() + " from " + message.getFrom());
        if (message.getContent().equals(TwoPhaseMessage.Prepared.toString())) {
            String preparedRM = message.getFrom();
            // if the message is from an RM managed by the TM
            if (resourceManagers.contains(preparedRM)) {
                this.preparedRMs.add(preparedRM);
                // Tracing
                specTmPrepared.add(preparedRM);
                spec.commitChanges("TMRcvPrepared");
            }
        }
    }

    protected boolean checkCommit() {
        System.out.println("TM rms = " + this.preparedRMs);
        return this.preparedRMs.size() >= this.resourceManagers.size();
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        System.out.println("TM sends Commits");
        // sends Commits to all RM
        for (String rmName : resourceManagers) {
            this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.Commit.toString(), 0));
        }
        // Tracing
        specMessages.add(Map.of("type", TwoPhaseMessage.Commit.toString()));
        spec.commitChanges("TMCommit");
        // Shutdown
        this.shutdown();
    }
}
