package org.lbee.protocol;

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
    // Timeout for receiving messages
    private final static int RECEIVE_TIMEOUT = 100;
    // Abort if not all RMs sent before ABORT_TIMEOUT
    private final static int ABORT_TIMEOUT = 100;

    // Resource managers managed by TM
    private final Set<String> resourceManagers;
    // Number of resource managers prepared to commit
    private final Collection<String> preparedRMs;

    // Tracing variables
    private final VirtualField traceMessages;
    private final VirtualField traceTmPrepared;
    private final VirtualField traceState;

    public TransactionManager(NetworkManager networkManager, String name, List<String> resourceManagerNames,
            TLATracer tracer) {
        super(name, networkManager, tracer);
        this.resourceManagers = new HashSet<>(resourceManagerNames);
        // If we use a list (potentially containing duplicates) instead of a set, the
        // size of the list doesn't necessarily reflect the number of prepared RMs and
        // if the TM uses preparedRMs.size to decide the commit, uncorrect traces can be
        // obtained (if one the RMs sends two PREPARED messages before another RMs sends
        // its PREPARED message).
        // Even if preparedRMs.size doesn't neccesarily reflect the number of prepared
        // RMs when the commit decision was taken, increasing the commit duration might
        // lead to a valid trace because the last RM (not counted by nbPrepared when the
        // commit decision was taken) has time to send its PREPARED message before the
        // TM sends the commit message.
        this.preparedRMs = new ArrayList<>();
        // this.preparedRMs = new HashSet<>();
        this.traceMessages = tracer.getVariableTracer("msgs");
        this.traceTmPrepared = tracer.getVariableTracer("tmPrepared");
        this.traceState = tracer.getVariableTracer("tmState");
    }

    @Override
    public void run() throws IOException {
        boolean done = false;
        long startTime = System.currentTimeMillis();
        // log that implicitly the state is init, no messages have been sent or received
        traceState.set("init");
        traceTmPrepared.clear();
        traceMessages.clear();
        tracer.log();
        // keep receiving messages until all RMs are prepared or they take too long to
        // send PREPARED
        while (!done) {
            // block on receiving message until timeout, retry if timeout
            boolean messageReceived = false;
            do {
                // Abort if not all RMs sent PREPARED before ABORT_TIMEOUT.
                // This test should be done before receiving a message, otherwise the TM might
                // sent an abort even if all RMs are prepared.
                if (System.currentTimeMillis() - startTime > ABORT_TIMEOUT) {
                    this.abort();
                    done = true;
                    break;
                }
                try {
                    Message message = networkManager.receive(this.name, RECEIVE_TIMEOUT);
                    this.handleMessage(message);
                    messageReceived = true;
                } catch (TimeOutException e) {
                    System.out.println("TM received TIMEOUT");
                }
            } while (!messageReceived);

            if (checkAllPrepared()) {
                this.commit();
                done = true;
            }
        }
        System.out.println("-- TM  shutdown");
    }

    /**
     * Handles the message received from an RM (corresponds to the action
     * TMRcvPrepared).
     * Only PREPARED messages from RMs managed by the TM are handled.
     * The RM sending the message is added to the preparedRMs set.
     */
    private void handleMessage(Message message) throws IOException {
        if (message.getContent().equals(TwoPhaseMessage.Prepared.toString())) {
            String preparedRM = message.getFrom();
            // if the message is from an RM managed by the TM
            if (resourceManagers.contains(preparedRM)) {
                this.preparedRMs.add(preparedRM);
                // trace the state change
                traceTmPrepared.add(preparedRM); // the RM is added to the set of prepared RMs
                tracer.log("TMRcvPrepared"); // log corresponding event
            }
        }

        System.out.println(
                "TM received " + message.getContent() + " from " + message.getFrom() + " => " + this.preparedRMs);
    }

    /**
     * @TLAAction TMAbort
     * @throws IOException
     */
    private void abort() throws IOException {
        // trace the state change
        traceMessages.add(Map.of("type", TwoPhaseMessage.Abort.toString())); // the abort message is added to the set of
                                                                             // messages
        traceState.set("done"); // the state is set to done
        // should log before the message is sent
        tracer.log("TMAbort"); // log event
        // sends Abort to all RMs
        for (String rmName : resourceManagers) {
            this.networkManager.send(new Message(this.name, rmName, TwoPhaseMessage.Abort.toString(), 0));
        }

        System.out.println("TM sends Abort");
    }

    protected boolean checkAllPrepared() {
        // System.out.println("TM check commit (rms = " + this.preparedRMs + ")");
        return this.preparedRMs.size() >= this.resourceManagers.size();
    }

    /**
     * @TLAAction TMCommit
     */
    private void commit() throws IOException {
        // add Add operator for Messages to the trace (corresponding to sending a
        // message)
        traceMessages.add(Map.of("type", TwoPhaseMessage.Commit.toString()));
        // we can also trace the state
        traceState.set("done");
        // should log before the message is sent
        tracer.log("TMCommit");
        // sends Commits to all RM
        for (String rmName : resourceManagers) {
            this.networkManager.send(new Message(this.name, rmName, TwoPhaseMessage.Commit.toString(), 0));
        }
        System.out.println("TM sent Commits");
    }
}
