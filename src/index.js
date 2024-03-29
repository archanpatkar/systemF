#!/usr/bin/env node
const readline = require('readline');
const { Interpreter, modes } = require("./eval");

const machine = new Interpreter();
const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout,
  prompt: 'sysf> '
});

console.log(
`
..%%%%...%%..%%...%%%%...%%%%%%..%%%%%%..%%...%%..%%%%%%.
.%%.......%%%%...%%........%%....%%......%%%.%%%..%%.....
..%%%%.....%%.....%%%%.....%%....%%%%....%%.%.%%..%%%%...
.....%%....%%........%%....%%....%%......%%...%%..%%.....
..%%%%.....%%.....%%%%.....%%....%%%%%%..%%...%%..%%.....   
`)
console.log("sysf (System F - Polymorphic Lambda Calculus) 0.0.1");
console.log("");

rl.prompt();

rl.on('line', (input) => {
    if(input == "help") {
        console.log("Type mode <m> where m in [value, name, need] to change evaluation method")
        console.log("Type 'clear' to clean the console")
        console.log("Type 'exit' or Ctrl + c to exit")
    }
    else if(input == "clear") console.clear();
    else if(input == "exit") {
        rl.close();
        console.log("");
        console.log("Goodbye!");
        return;
    }
    else if(input.startsWith("mode")) {
        let mode = modes[input.split(" ")[1]];
        if(mode) machine.setMode(mode)
        else console.log("Please specify a proper mode");
    }
    else {
        try {
            const {output, type} = machine.evaluate(input);
            console.log(`${type}: ${output}`);
        }
        catch (e) {
            console.log(`Error: ${e.message}`)
        }
    }
    rl.prompt();
});