package org.lbee.twophase;

import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class JFRPrinter {


    public static void main(String[] args) throws InterruptedException, IOException {

        // Read JFR events from files
        final List<RecordedEvent> events = new ArrayList<>();
        for (String path : args) {
            events.addAll(RecordingFile.readAllEvents(Path.of(path)));
        }

        System.out.printf("Start printing events at '%s'...\n", String.join(",", args));

        //final List<RecordedEvent> events = RecordingFile.readAllEvents(Path.of(path));

        // Order events chronologically based on the logical clock
        final ArrayList<RecordedEvent> tlaEvents =
            events.stream().filter(e -> e.getEventType().getName().equals("app.TLAEvent") || e.getEventType().getName().equals("app.NestedTLAEvent"))
            .sorted(Comparator.comparingLong(o -> o.getLong("clock")))
            .collect(Collectors.toCollection(ArrayList::new));

        System.out.printf("Get %s events.\n", tlaEvents.size());

        for (RecordedEvent event : tlaEvents) {
            System.out.printf("%s", event.toString());
        }
    }

}
