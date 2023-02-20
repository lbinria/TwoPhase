package org.lbee.twophase;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

public class TLALogger {

    // Local logical clock
    private long clock;

    private final List<App2TLA.TLAEvent> events;

    public TLALogger() {
        events = new ArrayList<>();
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
            events.add(new App2TLA.TLAEvent(obj.getName(), annot.name(), value, obj.getClock().getValue(), clock));
        } catch (NoSuchFieldException e) {
            // Do nothing (bad practice just for avoid throws exception on top and top and top...)
            System.out.println("ERROR: NoSuchFieldException");
        }
    }

    public <T extends TLANamedProcess, VType> void log(T obj, String key, String value) {
        events.add(new App2TLA.TLAEvent(obj.getName(), key, value, obj.getClock().getValue(), clock));
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
        for (App2TLA.TLAEvent event : events) {
            event.commit();
        }
        events.clear();
        clock++;
    }

}
