forbid(
  principal in a::"\0\0",
  action == Action::"action",
  resource is a
) when {
  true && ({"": [[]]} == {"": false})
};
