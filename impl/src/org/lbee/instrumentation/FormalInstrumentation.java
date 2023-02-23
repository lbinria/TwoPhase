package org.lbee.instrumentation;

import org.lbee.instrumentation.jfr.App2TLA;

import java.util.*;
import java.util.function.Supplier;

public class FormalInstrumentation<TProducer extends TraceProducer> {

    // Instrumentation guid
    private final String guid;

    // Local clock
    private final InstrumentationClock clock;
    // Instrumented values
    private final HashMap<String, FormalVariable<TProducer>> instrumentedValues;

    public InstrumentationClock getClock() {
        return this.clock;
    }

    public void sync(long clock) {
        this.clock.sync(clock);
    }

    public FormalInstrumentation(boolean logicClock) {
        this.guid = UUID.randomUUID().toString();
        this.instrumentedValues = new HashMap<>();
        this.clock = logicClock ? new LogicalClock() : new RealTimeClock();
    }

    public FormalVariable<TProducer> add(String name, Supplier<? extends FormalVariable<TProducer>> ctor) {
        // Construct object from type parameter
        FormalVariable<TProducer> instrumentedValue = Objects.requireNonNull(ctor).get();
        // Set name of the variable linked to the instrumented value
        instrumentedValue.setName(name);
        // Add to instrumented values
        this.instrumentedValues.put(name, instrumentedValue);
        return instrumentedValue;
    }

    public FormalVariable<TProducer> get(String name) {
        return this.instrumentedValues.get(name);
    }

    /**
     * Sync log to an action
     * @param action
     */
    public void syncCommit(Runnable action) {
        action.run();
        this.commit2();
    }


    /**
     * Commit logs
     */
    public void commit2() {
        // All events are committed at the same logical time (sync)
        long clock = this.clock.getValue();

        for (Map.Entry<String, FormalVariable<TProducer>> entry : this.instrumentedValues.entrySet()) {
            entry.getValue().commit(this.guid, clock);
        }

        this.clock.sync(clock);
    }

}
