//@ check-pass

pub trait HLSNamedPorts {}

pub struct HLSLevel2 {
    router: RouterROM,
    debugs: [HLSTester; 2],
}

pub struct HLSTester;

impl HLSNamedPorts for HLSTester {}

impl Default for HLSTester {
    fn default() -> Self {
        HLSTester
    }
}

impl Default for HLSLevel2 {
    fn default() -> Self {
        let debugs = [Default::default(), Default::default()];
        let router = RouterROM::new([&debugs[0], &debugs[1]]);
        Self { router, debugs }
    }
}

pub struct RouterROM;

impl RouterROM {
    pub fn new(downstream_devices: [&dyn HLSNamedPorts; 2]) -> Self {
        RouterROM
    }
}

fn main() {}
