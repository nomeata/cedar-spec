forbid(
  principal is hNNNN::a in hNNNN::a::"b",
  action in [hNNNN::Action::"action"],
  resource is hNNNN::a in hNNNN::a::"b"
) when {
  (true && ([[false, Ah200::""], context][""])) && principal
};
