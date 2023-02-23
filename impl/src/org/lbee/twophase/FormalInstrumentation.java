package org.lbee.twophase;

import java.util.*;
import java.util.function.Supplier;

public class FormalInstrumentation<TProducer extends TraceProducer> {

    // Local clock
    private final InstrumentationClock clock;
    //
    private final List<App2TLA.TLAEvent> events;
    // Instrumented values
    private final HashMap<String, FormalValue<TProducer>> instrumentedValues;

    public InstrumentationClock getClock() {
        return this.clock;
    }

    public void sync(long clock) {
        this.clock.sync(clock);
    }

    public FormalInstrumentation(boolean logicClock) {
        this.instrumentedValues = new HashMap<>();
        this.clock = logicClock ? new LogicalClock() : new RealTimeClock();
        this.events = new ArrayList<>();
    }

    public FormalValue<TProducer> add(String name, Supplier<? extends FormalValue<TProducer>> ctor) {
        // Construct object from type parameter
        FormalValue<TProducer> instrumentedValue = Objects.requireNonNull(ctor).get();
        // Set name of the variable linked to the instrumented value
        instrumentedValue.setName(name);
        // Add to instrumented values
        this.instrumentedValues.put(name, instrumentedValue);
        return instrumentedValue;
    }

    /*
    public <T extends TLANamedProcess, VType> void log(String key, String value) {
        events.add(new App2TLA.TLAEvent(key, value, this.clock.getValue()));
    }
    */

    public FormalValue<TProducer> get(String name) {
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
    /*
    public void commit() {
        // All events are committed at the same logical time (sync)
        long clock = this.clock.getValue();

        for (App2TLA.TLAEvent event : events) {
            event.setClock(clock);
            event.commit();
        }
        this.clock.sync(clock);
        events.clear();
    }
    */

    public void commit2() {
        // All events are committed at the same logical time (sync)
        long clock = this.clock.getValue();

        for (Map.Entry<String, FormalValue<TProducer>> entry : this.instrumentedValues.entrySet()) {
            entry.getValue().commit(clock);
        }

        this.clock.sync(clock);
    }

}
