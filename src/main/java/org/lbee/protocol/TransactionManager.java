package org.lbee.protocol;

import org.lbee.helpers.Helper;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;
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
    private final static int PROBABILITY_TO_ABORT = 100;
    // Resource managers managed by TM (as specified in the configuration)
    private final Set<String> resourceManagers;
    // Number of resource managers prepared to commit
    private final Collection<String> preparedRMs;

    private final VirtualField specMessages;
    private final VirtualField specTmPrepared;

    public TransactionManager(NetworkManager networkManager, String name, List<String> resourceManagerNames,
    TLATracer spec) {
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
        this.specMessages = spec.getVariable("msgs");
        this.specTmPrepared = spec.getVariable("tmPrepared");
    }

    @Override
    public void run() throws IOException {
        do {
            // Abort with some probablity
            this.abort();
            if (!this.isShutdown()) {
                // block on receiving message until timeout, retry if timeout
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
                    this.commit();
                }
            }
        } while (!this.isShutdown());
    }

    /**
     * @TLAAction TMAbort
     */
    private void abort() throws IOException {
        int possibleAbort = Helper.next(PROBABILITY_TO_ABORT);
        if (possibleAbort == 1) {
            // Tracing
            specMessages.add(Map.of("type", TwoPhaseMessage.Abort.toString()));
            spec.commitChanges("TMAbort");
            // sends Abort to all RM
            for (String rmName : resourceManagers) {
                this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.Abort.toString(), 0));
            }

            this.shutdown();

            System.out.println("TM sends Abort");
        }
    }

    protected void receive(Message message) throws IOException {
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

        System.out.println("TM received " + message.getContent() + " from " + message.getFrom());
    }

    protected boolean checkCommit() {
        // System.out.println("TM check commit (rms = " + this.preparedRMs + ")");
        return this.preparedRMs.size() >= this.resourceManagers.size();
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        // Tracing
        specMessages.add(Map.of("type", TwoPhaseMessage.Commit.toString()));
        spec.commitChanges("TMCommit");

        // sends Commits to all RM
        for (String rmName : resourceManagers) {
            this.networkManager.send(new Message(this.getName(), rmName, TwoPhaseMessage.Commit.toString(), 0));
        }

        System.out.println("TM sent Commits");

        this.shutdown();
    }
}
