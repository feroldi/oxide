
trait Port {
    type Kind;
}

enum Value {
    I32,
    I64,
}

enum State {
    Mem,
}

struct Input {

}

struct InputPorts {
    ports: Vec<bool>,
}

struct OutputPorts {
    used: bool,
}

struct Node {
    inputs: InputPorts,
    outputs: OutputPorts,
}

#[cfg(test)]
mod test {
}
