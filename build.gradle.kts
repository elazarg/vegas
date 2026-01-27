plugins {
    alias(libs.plugins.kotlin.jvm)
    `java-library`
    `maven-publish`
    application
}

repositories {
    mavenCentral()
}

dependencies {
    implementation(libs.lsp4j)
    implementation(libs.lsp4j.jsonrpc)
    implementation(libs.classgraph)
    implementation(libs.antlr.runtime)
    testImplementation(libs.kotest.runner)
    testImplementation(libs.kotest.assertions)
    testImplementation(libs.kotest.property)
}

group = "org.vegas"
version = "0.1"

// AstTranslator.java lives in src/main/kotlin — make the Java compiler see it
sourceSets {
    main {
        java.srcDir("src/main/kotlin")
    }
}

kotlin {
    jvmToolchain(25)
}

application {
    mainClass.set("vegas.MainKt")
}

tasks.test {
    useJUnitPlatform()
}

publishing {
    publications.create<MavenPublication>("maven") {
        from(components["java"])
    }
}

tasks.register<Jar>("fatJar") {
    archiveClassifier.set("all")
    manifest {
        attributes["Main-Class"] = "vegas.MainKt"
    }
    from(sourceSets.main.get().output)
    dependsOn(configurations.runtimeClasspath)
    from({
        configurations.runtimeClasspath.get().map { if (it.isDirectory) it else zipTree(it) }
    })
    exclude("META-INF/*.SF", "META-INF/*.DSA", "META-INF/*.RSA")
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
}

tasks.register<Copy>("copyLspJar") {
    from(tasks.named<Jar>("fatJar"))
    into(layout.projectDirectory.dir("lsp/server"))
    rename { "vegas.jar" }
}
