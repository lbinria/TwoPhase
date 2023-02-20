package org.lbee.twophase;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;

import java.util.List;

public class App2TLA {

    @Label("TLAEvent")
    @Name("app.TLAEvent")
    @Category("TwoPhase")
    @StackTrace(false)
    static class TLAEvent extends jdk.jfr.Event {

        @Label("localClock")
        long localClock;
        @Label("eventClock")
        long eventClock;
        @Label("sender")
        String sender;
        @Label("key")
        String key;
        @Label("val")
        String val;

        public TLAEvent(String sender, String key, Object val, long localClock, long eventClock) {
            this.localClock = localClock;
            this.eventClock = eventClock;
            this.sender = sender;
            this.key = key;
            this.val = val.toString();
            System.out.printf("Log event %s.%s = %s.\n", sender, key, val.toString());
        }

    }

}
