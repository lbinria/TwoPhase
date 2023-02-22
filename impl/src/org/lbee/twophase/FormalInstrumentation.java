package org.lbee.twophase;

import java.util.*;
import java.util.function.Supplier;

public class FormalInstrumentation<TOut extends CommitEvent> {

    // Local logical clock
    private final InstrumentationClock clock;
    private final List<App2TLA.TLAEvent> events;
    private final HashMap<String, IFormalValue<TOut>> instrumentedValues;

    public InstrumentationClock getClock() {
        return this.clock;
    }

    public FormalInstrumentation(boolean logicClock) {
        this.instrumentedValues = new HashMap<>();
        this.clock = logicClock ? new LogicalClock() : new RealTimeClock();
        this.events = new ArrayList<>();
    }

    public IFormalValue<TOut> add(String name, Supplier<? extends IFormalValue<TOut>> ctor) {
        // Construct object from type parameter
        IFormalValue<TOut> instrumentedValue = Objects.requireNonNull(ctor).get();
        instrumentedValue.setName(name);
        // Add to instrumented values
        this.instrumentedValues.put(name, instrumentedValue);
        return instrumentedValue;
    }


    public <T extends TLANamedProcess, VType> void log(String key, String value) {
        events.add(new App2TLA.TLAEvent(key, value, this.clock.getValue()));
    }

    public IFormalValue<TOut> get(String name) {
        return this.instrumentedValues.get(name);
    }

    /**
     * Sync log to an action
     * @param action
     */
    public void syncCommit(Runnable action) {
        action.run();
        commit();
    }


    /**
     * Commit logs
     */
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

    public void commit2() {
        // All events are committed at the same logical time (sync)
        long clock = this.clock.getValue();

        for (Map.Entry<String, IFormalValue<TOut>> entry : this.instrumentedValues.entrySet()) {
            entry.getValue().commit(clock);
        }

        this.clock.sync(clock);
    }

}
