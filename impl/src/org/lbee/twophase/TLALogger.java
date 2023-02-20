package org.lbee.twophase;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

public class TLALogger {

    // Local logical clock
    private LogicalClock clock;
    private final List<App2TLA.TLAEvent> events;

    public TLALogger(LogicalClock clock) {
        events = new ArrayList<>();
        this.clock = clock;
    }

    /**
     * Notify change of TLA variable
     * @param obj
     * @param fieldName
     * @param value
     * @param <T>
     * @param <VType>
     */
    public <T extends TLANamedProcess, VType> void notify(T obj, String fieldName, VType value) {
        try {
            // Get field
            Field field = obj.getClass().getDeclaredField(fieldName);
            field.setAccessible(true);
            // Get TLAVariable annotation on the field
            TLAVariable annot = field.getAnnotation(TLAVariable.class);
            // Log event
            // TODO make an abstract log layer
            events.add(new App2TLA.TLAEvent(obj.getName(), annot.name(), value, this.clock.getValue()));
        } catch (NoSuchFieldException e) {
            // Do nothing (bad practice just for avoid throws exception on top and top and top...)
            System.out.println("ERROR: NoSuchFieldException");
        }
    }

    public <T extends TLANamedProcess, VType> void log(T obj, String key, String value) {
        events.add(new App2TLA.TLAEvent(obj.getName(), key, value, this.clock.getValue()));
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
        events.clear();
    }

}
