use crate::types;
use crate::tid_list;

pub struct InputEdgeLabel(i16);
pub struct InputNodeLabel(i16);
pub struct InputNodeId(i16);

pub struct DatabaseTreeEdge {
	pub edgelabel: types::EdgeLabel,
	pub tonode: types::NodeId,
}

pub struct DatabaseTreeNode {
	pub nodelabel: types::NodeLabel,
	//pub edges: &'a [DatabaseTreeEdge], // This is giving lifetime issues that I still need to solve
	pub mark: types::PatternMask, // Might not want these two here
	pub startmark: types::PatternMask,
}

impl DatabaseTreeNode {
	pub fn new(nodelabel: types::NodeLabel /*, edges: &[DatabaseTreeEdge] */) -> DatabaseTreeNode {
		DatabaseTreeNode {
			nodelabel,
			//edges,
			mark: types::PatternMask(1),
			startmark: types::PatternMask(1)
		}
	}
}

pub struct DatabaseTree {
	pub tid: types::Tid,
	pub nodes: Vec<DatabaseTreeNode>,
	edges: Vec<DatabaseTreeEdge>, // May eventually convert to a Box<[DatabaseTreeEdge]>
}

impl DatabaseTree {
	pub fn new(tid: types::Tid) -> DatabaseTree {
		DatabaseTree { tid, nodes: Vec::new(), edges: Vec::new() }
	}
}

pub struct DatabaseNodeLabel {
	pub input_node_label: InputNodeLabel,
	pub frequency: types::Frequency,
	pub occurrence_count: types::Frequency,
	pub frequent_edge_labels: Vec<types::EdgeLabel>,
	last_tid: types::Tid, // Would like to remove, is only used while reading
}

pub struct DatabaseEdgeLabel {
	pub input_edge_label: InputEdgeLabel,
	pub to_node_label: types::NodeLabel,
	pub from_node_label: types::NodeLabel,
	pub edge_label: types::EdgeLabel,
	pub frequency: types::Frequency,
	pub occurrence_count: types::Frequency,
	pub tid_list: tid_list::TidList,
	last_tid: types::Tid, // similar
}

pub struct Database {
	pub trees: Vec<DatabaseTree>,
	pub node_labels: Vec<DatabaseNodeLabel>,
	pub edge_labels: Vec<DatabaseEdgeLabel>,
	pub largest_n_nodes: u32,
	pub largest_n_edges: u32,
	pub edge_labels_indexes: Vec<types::EdgeLabel>,
}
