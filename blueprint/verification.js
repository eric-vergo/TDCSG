// The hosted release supplies verification.json after its isolated comparator succeeds.
document.addEventListener("DOMContentLoaded", async () => {
  const history = Array.from(document.querySelectorAll("p a")).find(link =>
    link.textContent === "Actions history" && link.href === "https://github.com/eric-vergo/TDCSG/actions");
  if (!history) return;
  const paragraph = history.closest("p");
  const home = Array.from(paragraph.querySelectorAll("a")).find(link => link.textContent === "site home");
  if (!home) return;
  const url = new URL("verification.json", home.href);
  const status = document.createElement("p");
  status.setAttribute("role", "status");
  paragraph.after(status);
  const fallback = "This preview has no hosted comparator verdict.";
  try {
    const response = await fetch(url, { cache: "no-store" });
    if (!response.ok) throw new Error("Missing verification record");
    const record = await response.json();
    const expected = ["FiveDisk.finite_iff", "FiveDisk.infinite_orbit_zero", "FiveDisk.supremum_finite"];
    if (record.status !== "passed" || !/^[a-f0-9]{40}$/.test(record.commit) ||
        !/^https:\/\/github\.com\/eric-vergo\/TDCSG\/actions\/runs\/\d+\/?$/.test(record.run_url) ||
        !Array.isArray(record.theorems) || record.theorems.length !== expected.length ||
        !expected.every(name => record.theorems.includes(name))) throw new Error("Invalid verification record");
    const commit = document.createElement("a");
    commit.textContent = record.commit.slice(0, 12);
    commit.href = "https://github.com/eric-vergo/TDCSG/commit/" + record.commit;
    const run = document.createElement("a");
    run.textContent = "View the Linux verification run";
    run.href = record.run_url;
    const recordLink = document.createElement("a");
    recordLink.href = url.href;
    recordLink.textContent = "Download the verification record";
    status.append("All three statements passed independent replay at commit ", commit, ". ", run, ". ", recordLink, ".");
  } catch {
    status.textContent = fallback;
  }
});
