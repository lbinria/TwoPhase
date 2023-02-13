package org.lbee.twophase;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;

import java.util.ArrayList;
import java.util.List;

public class App2TLA {

    @Label("TLAEvent")
    @Name("app.TLAEvent")
    @Category("TwoPhase")
    @StackTrace(false)
    static class TLAEvent extends jdk.jfr.Event {

        @Label("clock")
        long clock;
        @Label("sender")
        String sender;
        @Label("key")
        String key;
        @Label("val")
        String val;

        public TLAEvent(String sender, String key, Object val, long clock) {
            this.clock = clock;
            this.sender = sender;
            this.key = key;
            this.val = val.toString();
            System.out.printf("Broadcast event %s.%s = %s.\n", sender, key, val.toString());
        }

    }

    @Label("NestedTLAEvent")
    @Name("app.NestedTLAEvent")
    @Category("TwoPhase")
    @StackTrace(false)
    static class NestedTLAEvent extends jdk.jfr.Event {

        @Label("events")
        List<TLAEvent> events;
        @Label("events2")
        TLAEvent[] events2;

        public NestedTLAEvent(List<TLAEvent> events) {
            this.events = events;
            this.events2 = events.toArray(new TLAEvent[0]);
        }

    }

}
