mod types;
mod tid_list;
mod database;

fn main() {
    println!("Hello, world!");
    
    let db = database::Database::read("");
}
