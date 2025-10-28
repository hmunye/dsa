#![allow(dead_code)]

fn linear_search<T, Q>(nums: &[T], target: &Q) -> Option<usize>
where
    T: std::borrow::Borrow<Q> + PartialEq,
    Q: PartialEq,
{
    #[allow(clippy::manual_find)]
    #[allow(clippy::needless_range_loop)]
    for i in 0..nums.len() {
        if nums[i].borrow() == target {
            return Some(i);
        }
    }

    None
}

fn binary_search<T, Q>(nums: &[T], target: &Q) -> Option<usize>
where
    T: std::borrow::Borrow<Q> + Ord,
    Q: Ord,
{
    let mut lo = 0;
    let mut hi = nums.len();

    while lo < hi {
        let m = lo + (hi - lo) / 2;

        if nums[m].borrow() == target {
            return Some(m);
        } else if nums[m].borrow() < target {
            lo = m + 1;
        } else {
            hi = m;
        }
    }

    None
}

fn selection_sort<T: Ord>(nums: &mut [T]) {
    for i in 0..nums.len() {
        let mut min = i;

        for j in min + 1..nums.len() {
            if nums[j] < nums[min] {
                min = j;
            }
        }

        if min != i {
            nums.swap(i, min);
        }
    }
}

fn insertion_sort<T: Ord>(nums: &mut [T]) {
    for i in 1..nums.len() {
        let mut j = i;

        while j > 0 && nums[j - 1] > nums[j] {
            nums.swap(j - 1, j);
            j -= 1;
        }
    }
}

fn bubble_sort<T: Ord>(nums: &mut [T]) {
    for i in 0..nums.len() {
        for j in 0..nums.len() - i - 1 {
            if nums[j + 1] < nums[j] {
                nums.swap(j + 1, j);
            }
        }
    }
}

fn quick_sort<T: Ord>(nums: &mut [T]) {
    fn partition<T: Ord>(arr: &mut [T]) -> usize {
        let pivot = arr.len() - 1;
        let mut i = 0;

        for j in 0..arr.len() - 1 {
            if arr[j] < arr[pivot] {
                arr.swap(j, i);
                i += 1;
            }
        }

        arr.swap(pivot, i);
        i
    }

    if nums.len() > 1 {
        let pivot_idx = partition(nums);

        quick_sort(&mut nums[..pivot_idx]);
        quick_sort(&mut nums[pivot_idx + 1..]);
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Point {
    x: usize,
    y: usize,
}

fn solve(maze: &[&str], wall: &str, start: Point, end: Point) -> Vec<Point> {
    fn walk(
        maze: &[&str],
        wall: &str,
        curr: Point,
        end: Point,
        seen: &mut [Vec<bool>],
        path: &mut Vec<Point>,
    ) -> bool {
        if curr == end {
            // Push the final point in the path.
            path.push(end);

            return true;
        }

        // Check if current point is in-bounds.
        if let Some(y) = maze.get(curr.y)
            && let Some(x) = y.get(curr.x..curr.x + 1)
        {
            // Check if current point is on a wall.
            if x == wall {
                return false;
            }

            // Check if current point as been seen before.
            if seen[curr.y][curr.x] {
                return false;
            }

            seen[curr.y][curr.x] = true;
            path.push(curr);

            // Check left.
            if walk(
                maze,
                wall,
                Point {
                    x: curr.x - 1,
                    y: curr.y,
                },
                end,
                seen,
                path,
            ) {
                return true;
            }

            // Check right.
            if walk(
                maze,
                wall,
                Point {
                    x: curr.x + 1,
                    y: curr.y,
                },
                end,
                seen,
                path,
            ) {
                return true;
            }

            // Check down.
            if walk(
                maze,
                wall,
                Point {
                    x: curr.x,
                    y: curr.y - 1,
                },
                end,
                seen,
                path,
            ) {
                return true;
            }

            // Check up.
            if walk(
                maze,
                wall,
                Point {
                    x: curr.x,
                    y: curr.y + 1,
                },
                end,
                seen,
                path,
            ) {
                return true;
            }

            path.pop();
        }

        false
    }
    let mut path: Vec<Point> = Vec::new();
    // TODO: Bit-vector would be better.
    let mut seen = vec![vec![false; maze[0].len()]; maze.len()];

    walk(maze, wall, start, end, &mut seen, &mut path);

    path
}

fn adj_dfs(adj: &[Vec<usize>], start: usize) -> Vec<usize> {
    fn dfs(adj: &[Vec<usize>], vertex: usize, out: &mut Vec<usize>, seen: &mut Vec<bool>) {
        if seen[vertex] {
            return;
        }

        out.push(vertex);
        seen[vertex] = true;

        for edge in &adj[vertex] {
            dfs(adj, *edge, out, seen);
        }
    }

    let mut out = Vec::with_capacity(adj.len());
    let mut seen = vec![false; adj.len()];

    dfs(adj, start, &mut out, &mut seen);

    out
}

fn adj_bfs(adj: &[Vec<usize>], start: usize) -> Vec<usize> {
    let mut out = Vec::with_capacity(adj.len());
    let mut seen = vec![false; adj.len()];

    let mut queue = std::collections::VecDeque::with_capacity(adj.len());

    queue.push_back(start);

    while let Some(vertex) = queue.pop_front() {
        if seen[vertex] {
            continue;
        }

        out.push(vertex);
        seen[vertex] = true;

        for edge in &adj[vertex] {
            queue.push_back(*edge);
        }
    }

    out
}

// TODO: use heap instead for *O*((v+e) log_v) time complexity instead of
// *O*(v^2 + e) time complexity.
fn dijkstra_list(adj: &[Vec<(usize, usize)>], source: usize, sink: usize) -> Vec<usize> {
    fn has_unvisited(seen: &[bool], dists: &[usize]) -> bool {
        for (i, seen) in seen.iter().enumerate() {
            if !*seen && dists[i] < usize::MAX {
                return true;
            }
        }

        false
    }

    fn shortest_unvisited(seen: &[bool], dists: &[usize]) -> usize {
        let mut idx = 0;
        let mut lowest_dist = usize::MAX;

        for (i, seen) in seen.iter().enumerate() {
            if *seen {
                continue;
            }

            if dists[i] < lowest_dist {
                lowest_dist = dists[i];
                idx = i;
            }
        }

        idx
    }

    let mut prev = vec![usize::MAX; adj.len()];
    let mut seen = vec![false; adj.len()];
    let mut dists = vec![usize::MAX; adj.len()];

    dists[source] = 0;

    while has_unvisited(&seen, &dists) {
        let vertex = shortest_unvisited(&seen, &dists);
        seen[vertex] = true;

        for (edge, weight) in &adj[vertex] {
            if seen[*edge] {
                continue;
            };

            let dist = dists[vertex] + *weight;
            if dist < dists[*edge] {
                dists[*edge] = dist;
                prev[*edge] = vertex;
            }
        }
    }

    let mut out = Vec::new();
    let mut curr = sink;

    while prev[curr] != usize::MAX {
        out.push(curr);
        curr = prev[curr];
    }

    out.push(source);
    out.reverse();

    out
}

fn main() {
    #[allow(clippy::disallowed_names)]
    let mut foo = [99, 1, 69420, 4, 1337, 71, 90, 420, 81, 3, 69];

    quick_sort(&mut foo);
    // bubble_sort(&mut foo);
    // insertion_sort(&mut foo);
    // selection_sort(&mut foo);

    println!("{foo:?}");

    assert_eq!(binary_search(&foo, &69), Some(3));
    assert_eq!(binary_search(&foo, &1336), None);
    assert_eq!(binary_search(&foo, &69420), Some(foo.len() - 1));
    assert_eq!(binary_search(&foo, &69421), None);
    assert_eq!(binary_search(&foo, &1), Some(0));
    assert_eq!(binary_search(&foo, &0), None);

    #[rustfmt::skip]
    let maze1 = [
        "##### #", 
        "#     #", 
        "# #####"
    ];
    println!(
        "Maze 1: {:?}",
        solve(&maze1, "#", Point { x: 1, y: 2 }, Point { x: 5, y: 0 })
    );

    #[rustfmt::skip]
    let maze2 = [
        "#####",
        "#   #",
        "# # #",
        "#   #",
        "#####"
    ];
    println!(
        "Maze 2: {:?}",
        solve(&maze2, "#", Point { x: 1, y: 3 }, Point { x: 3, y: 1 })
    );

    #[rustfmt::skip]
    let maze3 = [
        "#######",
        "#     #",
        "### # #",
        "#   # #",
        "# ### #",
        "#     #",
        "#######"
    ];
    println!(
        "Maze 3: {:?}",
        solve(&maze3, "#", Point { x: 1, y: 1 }, Point { x: 5, y: 5 })
    );

    #[rustfmt::skip]
    let maze4 = [
        "#####",
        "# # #",
        "# # #",
        "#   #",
        "#####"
    ];
    println!(
        "Maze 4: {:?}",
        solve(&maze4, "#", Point { x: 1, y: 3 }, Point { x: 3, y: 3 })
    );

    #[rustfmt::skip]
    let adj_list = vec![
        vec![1, 2],
        vec![0, 3],
        vec![0, 3],
        vec![1, 2],
    ];

    println!("graph DFS: {:?}", adj_dfs(&adj_list, 0));
    println!("graph BFS: {:?}", adj_bfs(&adj_list, 0));

    let adj_list = vec![
        vec![(1, 7), (2, 9), (3, 14)],
        vec![(0, 7), (2, 10), (4, 15)],
        vec![(0, 9), (1, 10), (3, 11), (4, 2)],
        vec![(0, 14), (2, 11), (4, 9)],
        vec![(1, 15), (2, 2), (3, 9)],
    ];

    println!(
        "Dijkstra's Shortest Path (0-4): {:?}",
        dijkstra_list(&adj_list, 0, 4)
    );
}
