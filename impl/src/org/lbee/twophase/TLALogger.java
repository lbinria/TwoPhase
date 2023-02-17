package org.lbee.twophase;

import java.lang.reflect.Field;

public class TLALogger {

    // Local logical clock
    private long clock;

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
            new App2TLA.TLAEvent(obj.getName(), annot.name(), value, clock).commit();
        } catch (NoSuchFieldException e) {
            // Do nothing (bad practice just for avoid throws exception on top and top and top...)
            System.out.println("ERROR: NoSuchFieldException");
        }
    }

    /**
     * Sync log to an action
     * @param action
     */
    public void sync(Runnable action) {
        clock++;
        action.run();
    }

    public void trigger() {
        clock++;
    }

}
