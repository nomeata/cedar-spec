@A("\0")
permit(
  principal == a::"rrr",
  action,
  resource is a in a::"rrr"
) when {
  true && (!([[], []] == []))
};
