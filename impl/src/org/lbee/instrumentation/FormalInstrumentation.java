package org.lbee.instrumentation;

import org.lbee.instrumentation.clock.InstrumentationClock;
import org.lbee.instrumentation.clock.LogicalClock;
import org.lbee.instrumentation.clock.RealTimeClock;

import java.util.HashMap;
import java.util.Objects;
import java.util.UUID;
import java.util.function.Supplier;

public class FormalInstrumentation<TProducer extends TraceProducer<?>> {

    // Instrumentation guid
    private final String guid;
    // Configuration
    private final FormalInstrumentationConfig configuration;
    // Local clock
    private final InstrumentationClock clock;
    // Instrumented values
    private final HashMap<String, TrackableVariable<?>> instrumentedValues;
    // Trace producer
    private final TProducer traceProducer;

    public InstrumentationClock getClock() {
        return this.clock;
    }

    public String getGuid() { return this.guid; }

    public void sync(long clock) {
        this.clock.sync(clock);
    }

    public FormalInstrumentation(FormalInstrumentationConfig configuration, TProducer traceProducer) {
        this.guid = UUID.randomUUID().toString();
        this.configuration = configuration;
        this.instrumentedValues = new HashMap<>();
        this.clock = configuration.isLogicClock() ? new LogicalClock() : new RealTimeClock();

        // TODO construct from configuration
        this.traceProducer = traceProducer;
        this.traceProducer.setIntrumentation(this);
    }

    /**
     * Create
     * @param name
     * @param ctor
     * @return
     */
    public TrackableVariable add(String name, Supplier<? extends TrackableVariable> ctor) {
        // Construct object from type parameter
        final TrackableVariable trackedVariable = Objects.requireNonNull(ctor).get();
        // Set name of the variable linked to the instrumented value
        trackedVariable.setName(name);
        trackedVariable.setTraceProducer(this.traceProducer);
        // Add to instrumented values
        this.instrumentedValues.put(name, trackedVariable);
        return trackedVariable;
    }

    /**
     * Get a tracked variable by name
     * @param name Tracked variable name
     * @return A tracked variable
     */
    public TrackableVariable get(String name) {
        return this.instrumentedValues.get(name);
    }

    /**
     * Sync log to an action
     * @param action
     */
    public void syncCommit(Runnable action) {
        action.run();
        this.commit();
    }

    /**
     * Commit logs
     */
    public void commit() {
        // All events are committed at the same logical time (sync)
        final long clock = this.clock.getValue();
        // Commit all previously produced traces
        this.traceProducer.commit(clock);
        // Resync clock
        this.clock.sync(clock);
    }

}
