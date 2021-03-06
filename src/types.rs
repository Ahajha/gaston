#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug, Copy, Clone)]
pub struct EdgeLabel(pub u8);
#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct NodeLabel(pub u8);
#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct NodeId(pub u16);
pub struct Depth(pub u32);
#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct Tid(pub u16);
pub type Frequency = u32;
#[derive(std::cmp::PartialEq, std::cmp::Eq, Debug)]
pub struct PatternMask(pub u32);

pub const NO_TID: Tid = Tid(u16::MAX);
pub const NO_EDGELABEL: EdgeLabel = EdgeLabel(u8::MAX);
pub const MAX_EDGELABEL: EdgeLabel = EdgeLabel(u8::MAX);
pub const MIN_EDGELABEL: EdgeLabel = EdgeLabel(u8::MIN);
pub const NO_NODELABEL: NodeLabel = NodeLabel(u8::MAX);
pub const NO_DEPTH: Depth = Depth(u32::MAX);
pub const NO_NODE: NodeId = NodeId(u16::MAX);
