package org.lbee.twophase;

import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordingFile;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class JFRPrinter {


    public static void main(String[] args) throws InterruptedException, IOException {

        String path = args[0];

        System.out.printf("Start printing events at '%s'...\n", path);

        // Read JFR events from file
        final List<RecordedEvent> events = RecordingFile.readAllEvents(Path.of(path));

        // Order events chronologically based on the system's clock (that hopefully has
        // sufficient precision).
        // TODO: Logical clock instead of real/global clock.
        ArrayList<RecordedEvent> tlaEvents =
            events.stream().filter(e -> e.getEventType().getName().equals("app.TLAEvent") || e.getEventType().getName().equals("app.NestedTLAEvent"))
            .sorted((o1, o2) -> o1.getStartTime().compareTo(o2.getStartTime()))
            .collect(Collectors.toCollection(ArrayList::new));

        System.out.printf("Get %s events.\n", tlaEvents.size());

        for (RecordedEvent event : tlaEvents) {
            System.out.printf("%s", event.toString());
        }
    }

}
