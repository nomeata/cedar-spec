@AL230("jj\0\0dd")
@hDDD("")
forbid(
  principal is a in a::"dd",
  action in [Action::""],
  resource is a in a::"dd"
) when {
  (true && (action in a::"dd")) && principal
};
