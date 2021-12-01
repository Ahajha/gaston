pub struct EdgeLabel(pub u8);
pub struct NodeLabel(pub u8);
pub struct NodeId(pub u16);
pub struct Depth(pub u32);
pub struct Tid(pub u16);
pub struct Frequency(pub u32);
pub struct PatternMask(pub u32);

pub const NO_TID: Tid = Tid(u16::MAX);
pub const NO_EDGELABEL: EdgeLabel = EdgeLabel(u8::MAX);
pub const MAX_EDGELABEL: EdgeLabel = EdgeLabel(u8::MAX);
pub const MIN_EDGELABEL: EdgeLabel = EdgeLabel(u8::MIN);
pub const NO_NODELABEL: NodeLabel = NodeLabel(u8::MAX);
pub const NO_DEPTH: Depth = Depth(u32::MAX);
pub const NO_NODE: NodeId = NodeId(u16::MAX);
