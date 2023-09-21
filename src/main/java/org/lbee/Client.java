package org.lbee;

import org.lbee.instrumentation.ConfigurationWriter;

import java.io.IOException;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Map;
import java.util.stream.IntStream;

/**
 * Client manager (transaction manager or resource manager)
 */
public class Client {

    public static void main(String[] args) throws IOException {

        if (args.length < 4) {
            System.out.println("Missing arguments. hostname, port, type={tm, rm} expected.");
            return;
        }

        // Get hostname, port and type of manager
        final String hostname = args[0];
        final int port = Integer.parseInt(args[1]);
        final String type = args[2];
        final String resourceManagerName = args[3];

        final Configuration config = new Configuration(args);
        // Some printing
        System.out.println(config);

        // Write config in file
        final String[] rmNames = IntStream.range(0, config.nResourceManager).mapToObj(i -> "rm-" + i).toArray(String[]::new);
        final Map<String, Object> mapConfig = Map.of("RM", rmNames);
        ConfigurationWriter.write("twophase.ndjson.conf", mapConfig);

        try (Socket socket = new Socket(hostname, port)) {

            final Manager manager;
            switch (type) {
                case "tm" -> manager = new TransactionManager(socket, config.tmConfig);
                case "rm" -> {
                    ResourceManager resourceManager = new ResourceManager(socket, resourceManagerName, "TM", config.rmConfig);
                    resourceManager.register();
                    manager = resourceManager;
                }
                default -> {
                    System.out.println("Expected type is tm or rm.");
                    return;
                }
            }

            do {
                // Execute manager
                manager.run();
            }
            while (!manager.isShutdown());

            // Send bye to server (kill the server thread)
            manager.networkManager.sendRaw("bye");

            // Print end of process
            System.out.println("shutdown.");

        } catch (UnknownHostException ex) {
            System.out.println("Server not found: " + ex.getMessage());
        } catch (IOException ex) {
            System.out.println("I/O error: " + ex.getMessage());
        }
    }

}
